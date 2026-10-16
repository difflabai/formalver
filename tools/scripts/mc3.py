#!/usr/bin/env python3
"""MC-3: compare the reachable graph of TLC (tla/MC_Graph.tla) with the
Prolog requirements model's (prolog/verification/graph_export.pl). MC-4:
the same comparison with the Lean machine's (`approval-lean graph`), which
writes the same format.

usage: mc3.py <tlc-edges.dump> <tlc-table.out> <prolog.txt> [label]

<tlc-edges.dump> is `tlc2.TLC -dump` of MC_Graph.cfg: each state is one
successful call (prev, lastOp, store). <tlc-table.out> is TLC's stdout for
MC_GraphTable.cfg, whose Table invariant prints every store with the calls
it rejects. Both are turned into graph_export.pl's text format and the
three sets (stores, rejected calls with their errors, successful edges)
must be equal. Exit 0 if equal; else print the first differences, for each
(store, call) with both sides' results. [label] names the third file's
model in the output (default Prolog).
"""
import re
import sys

# ---------------------------------------------------------------------------
# A reader for the TLA+ values TLC prints.
# ---------------------------------------------------------------------------

TOK = re.compile(r'\s*(<<|>>|\|->|:>|@@|"(?:[^"\\]|\\.)*"|-?\d+|[A-Za-z_][A-Za-z0-9_]*|[\[\]{}(),])')


def tokens(s):
    pos, out = 0, []
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            if s[pos:].strip() == "":
                break
            raise ValueError(f"bad token at {s[pos:pos + 40]!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


class Fn(dict):
    """A TLA+ function `(k1 :> v1 @@ ...)` or record."""

    def __hash__(self):
        return hash(tuple(sorted(self.items(), key=repr)))


def parse(s):
    ts = tokens(s)
    v, i = value(ts, 0)
    if i != len(ts):
        raise ValueError(f"trailing tokens: {ts[i:i + 5]}")
    return v


def value(ts, i):
    t = ts[i]
    if t == "<<":
        items, i = seq(ts, i + 1, ">>")
        return tuple(items), i
    if t == "{":
        items, i = seq(ts, i + 1, "}")
        return frozenset(items), i
    if t == "[":
        rec, i = Fn(), i + 1
        while ts[i] != "]":
            k = ts[i]
            assert ts[i + 1] == "|->", ts[i:i + 3]
            v, i = value(ts, i + 2)
            rec[k] = v
            if ts[i] == ",":
                i += 1
        return rec, i + 1
    if t == "(":
        fn, i = Fn(), i + 1
        while True:
            k, i = value(ts, i)
            assert ts[i] == ":>", ts[i:i + 3]
            v, i = value(ts, i + 1)
            fn[k] = v
            if ts[i] == "@@":
                i += 1
                continue
            assert ts[i] == ")", ts[i:i + 3]
            return fn, i + 1
    if t.startswith('"'):
        return t[1:-1], i + 1
    if re.fullmatch(r"-?\d+", t):
        return int(t), i + 1
    if t in ("TRUE", "FALSE"):
        return t == "TRUE", i + 1
    return t, i + 1  # model value


def seq(ts, i, close):
    items = []
    while ts[i] != close:
        v, i = value(ts, i)
        items.append(v)
        if ts[i] == ",":
            i += 1
    return items, i + 1


# ---------------------------------------------------------------------------
# TLA+ store -> graph_export.pl text
# ---------------------------------------------------------------------------

ACT = {"x": "x", "EMPTY": "empty", "TOOLONG": "too_long"}
ROLE = {"Agent": "agent", "Approver": "approver"}


def text_store(store):
    principals, requests, log, regs, revoked = store
    ps = sorted(
        f"{k},{p['acct']},{ROLE[p['role']]},{p['rid']},{p['from']},{p['pending']}"
        for k, p in principals.items()
        if p["reg"]
    )
    rs = []
    for r in requests:
        ap = f"{r['aidx']}/{r['aacct']}/{r['akey']}/{r['arid']}" if r["appr"] else "-"
        rj = f"{r['racct']}/{r['rkey']}/{r['rrid']}" if r["rj"] else "-"
        rs.append(f"{r['acct']},{r['key']},{r['rid']},{ACT[r['act']]},{ap},{rj}")
    return "|".join([
        ";".join(ps),
        ";".join(rs),
        ",".join(str(i) for i in log),
        str(regs),
        ",".join(str(g) for g in sorted(revoked)),
    ])


def text_call(op, args):
    out = [op]
    for a in args:
        if isinstance(a, str) and a in ACT:
            out.append(ACT[a])
        elif isinstance(a, str) and a in ROLE:
            out.append(ROLE[a])
        else:
            out.append(str(a))
    return ",".join(out)


def tlc_edges(path):
    """(store, call, store') for every successful call."""
    edges, cur = set(), {}

    def flush():
        if cur and cur["lastOp"][0] != "init":
            store = (cur["principals"], cur["requests"], cur["log"], cur["regs"], cur["revoked"])
            op, args = cur["lastOp"]
            edges.add((text_store(cur["prev"]), text_call(op, args), text_store(store)))

    block = []
    for ln in open(path):
        if ln.startswith("State "):
            if block:
                cur = state_vars(block)
                flush()
            block = []
        else:
            block.append(ln)
    if block:
        cur = state_vars(block)
        flush()
    return edges


def state_vars(lines):
    out, name, buf = {}, None, []
    for ln in lines:
        m = re.match(r"/\\ (\w+) = (.*)", ln)
        if m:
            if name:
                out[name] = parse(" ".join(buf))
            name, buf = m.group(1), [m.group(2)]
        elif name:
            buf.append(ln.strip())
    if name:
        out[name] = parse(" ".join(buf))
    return out


def tlc_table(path):
    stores, rejected = set(), set()
    text = open(path).read()
    # PrintT output spans lines; each starts with << "TABLE",
    for chunk in re.split(r'(?=<<\s*"TABLE",)', text)[1:]:
        # The value ends where TLC's own output resumes (a line not
        # starting with whitespace or a delimiter).
        m = re.search(r"\n(?=[A-Za-z@])", chunk)
        v = parse(chunk[: m.start()] if m else chunk)
        _, store, rej = v
        ts = text_store(store)
        stores.add(ts)
        for (call, err) in rej:
            rejected.add((ts, text_call(call[0], call[1:]), err))
    return stores, rejected


ACCOUNTS = ["o", "a1", "a2"]
KEYS = ["k1", "k2"]
ACTS = ["x", "empty", "too_long"]


def calls(nr):
    """Every call in a store with nr requests, in graph_export.pl's order."""
    out = []
    for c in ACCOUNTS:
        for k in KEYS:
            for a in ACCOUNTS:
                for r in ("agent", "approver"):
                    out.append(f"add,{c},{k},{a},{r}")
    out += [f"revoke,{c},{k}" for c in ACCOUNTS for k in KEYS]
    tri = [(p, s, k) for p in ACCOUNTS for s in ACCOUNTS for k in KEYS]
    out += [f"request,{p},{s},{k},{x}" for p, s, k in tri for x in ACTS]
    out += [f"approve,{p},{s},{k},{i},{x}" for p, s, k in tri for i in range(nr + 1) for x in ACTS]
    out += [f"reject,{p},{s},{k},{i}" for p, s, k in tri for i in range(nr + 1)]
    return out


def prolog(path):
    stores, rejected, edges = set(), set(), set()
    for ln in open(path):
        f = ln.rstrip("\n").split("\t")
        if f[0] == "S":
            stores.add(f[1])
        elif f[0] == "R":
            reqs = f[1].split("|")[1]
            nr = len(reqs.split(";")) if reqs else 0
            res = f[2].split(",")
            cs = calls(nr)
            assert len(cs) == len(res), (f[1], len(cs), len(res))
            for c, r in zip(cs, res):
                if r != "Ok":
                    rejected.add((f[1], c, r))
        elif f[0] == "E":
            edges.add((f[1], f[2], f[3]))
    return stores, rejected, edges


def main():
    dump, table, pl = sys.argv[1:4]
    label = sys.argv[4] if len(sys.argv) > 4 else "Prolog"
    t_edges = tlc_edges(dump)
    t_stores, t_rej = tlc_table(table)
    p_stores, p_rej, p_edges = prolog(pl)
    print(f"TLC:    {len(t_stores)} stores, {len(t_rej)} rejected calls, {len(t_edges)} edges")
    print(f"{label + ':':<8}{len(p_stores)} stores, {len(p_rej)} rejected calls, {len(p_edges)} edges")
    ok = True
    for name, a, b in (("stores", t_stores, p_stores), ("rejected calls", t_rej, p_rej), ("edges", t_edges, p_edges)):
        only_t, only_p = a - b, b - a
        if only_t or only_p:
            ok = False
            print(f"\n{name}: {len(only_t)} only in TLC, {len(only_p)} only in {label}")
            for x in sorted(only_t)[:5]:
                print("  TLC only:   ", x)
            for x in sorted(only_p)[:5]:
                print(f"  {label} only:", x)
    if ok:
        print(f"TLC and {label}: graphs equal")
        return 0
    # Per (store, call): both sides' results, for the first disagreements.
    def results(rej, edges):
        r = {}
        for s, c, e in rej:
            r.setdefault((s, c), set()).add("err " + e)
        for s, c, s1 in edges:
            r.setdefault((s, c), set()).add("ok -> " + s1)
        return r
    rt, rp = results(t_rej, t_edges), results(p_rej, p_edges)
    diff = sorted(k for k in set(rt) | set(rp) if rt.get(k) != rp.get(k))
    print(f"\n{len(diff)} (store, call) pairs disagree; first ones:")
    for k in diff[:10]:
        print(f"  store {k[0]}\n  call  {k[1]}\n    TLC:    {sorted(rt.get(k, {'ok (no edge: bound)'}))}\n    {label}: {sorted(rp.get(k, {'ok (no edge: bound)'}))}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
