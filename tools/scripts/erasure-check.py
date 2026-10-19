#!/usr/bin/env python3
"""Erasure check for a Verus "verified twin" (strategy.md §7, path A).

Strips the ghost code from the twin's lib.rs and requires the remaining
token stream to equal the upstream file's, except for the functions listed
in REWRITES.toml (each must carry a Kani equivalence harness) and the
attribute substitutions listed there.

usage: erasure-check.py <twin lib.rs> <upstream lib.rs> <REWRITES.toml>

What counts as ghost (removed from the twin):
- `verus! {` ... `}` wrappers (their contents are kept);
- the region between `// ---- verus twin: ghost-only additions` and
  `// ---- end ghost ----`;
- `requires` / `ensures` / `invariant` / `decreases` clauses, up to the body
  or the `;` of a trait method;
- named returns `-> (name: T)`, which become `-> T`;
- `proof { ... }` blocks and `let ghost ...;` statements;
- `spec fn` / `open spec fn` / `closed spec fn` / `proof fn` items;
- closure annotations: parameter types, `-> (b: T)` and the braces Verus
  needs around an annotated closure's body.
Comments are not tokens, so doc comments never cause a mismatch.
"""
import re
import sys
import tomllib

TOKEN = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<lcomment>//[^\n]*)
  | (?P<bcomment>/\*.*?\*/)
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>'(?:\\.|[^'\\])'(?!\w))
  | (?P<life>'[A-Za-z_]\w*)
  | (?P<num>\d[\w.]*)
  | (?P<ident>[A-Za-z_]\w*)
  | (?P<punct>::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\.\.=|\.\.|[{}()\[\];:,.<>=!&|*+\-/?#@%^~$])
    """,
    re.S | re.X,
)


def tokenize(src):
    out, pos = [], 0
    while pos < len(src):
        m = TOKEN.match(src, pos)
        if not m:
            raise SystemExit(f"tokenize: stuck at {src[pos:pos + 40]!r}")
        kind = m.lastgroup
        if kind not in ("ws", "lcomment", "bcomment"):
            out.append(m.group())
        pos = m.end()
    return out


OPEN = {"(": ")", "[": "]", "{": "}"}


def match_close(t, i):
    """Index of the bracket closing t[i]."""
    depth = 0
    for j in range(i, len(t)):
        if t[j] in OPEN:
            depth += 1
        elif t[j] in (")", "]", "}"):
            depth -= 1
            if depth == 0:
                return j
    raise SystemExit("unbalanced brackets")


CLAUSES = {"requires", "ensures", "invariant", "decreases"}


def strip_ghost(src):
    # Ghost header region (textual).
    src = re.sub(r"// ---- verus twin: ghost-only additions.*?// ---- end ghost ----\n",
                 "", src, flags=re.S)
    t = tokenize(src)
    out = []
    i = 0
    verus_stack = []  # indices in `out`-space depth of verus! wrappers
    depth = 0
    while i < len(t):
        tok = t[i]
        # verus! { ... }  -> contents
        if tok == "verus" and t[i + 1:i + 3] == ["!", "{"]:
            close = match_close(t, i + 2)
            t[close] = "\0"  # mark wrapper close for removal
            i += 3
            continue
        if tok == "\0":
            i += 1
            continue
        # spec / proof items: [pub] [open|closed] spec fn ... { } | ;
        if tok in ("spec", "proof") and i + 1 < len(t) and t[i + 1] == "fn":
            # drop preceding visibility / open / closed / broadcast
            while out and out[-1] in ("pub", "open", "closed", "broadcast"):
                out.pop()
            j = i
            while t[j] not in ("{", ";"):
                if t[j] in ("(", "["):
                    j = match_close(t, j)
                j += 1
            i = (match_close(t, j) if t[j] == "{" else j) + 1
            continue
        # proof { ... }
        if tok == "proof" and t[i + 1] == "{":
            i = match_close(t, i + 1) + 1
            continue
        # let ghost x = ...;
        if tok == "let" and t[i + 1] == "ghost":
            while t[i] != ";":
                i += 1
            i += 1
            continue
        # -> (name: T)  =>  -> T
        if tok == "->" and t[i + 1] == "(" and re.match(r"[A-Za-z_]\w*$", t[i + 2]) and t[i + 3] == ":":
            close = match_close(t, i + 1)
            out.append("->")
            out.extend(t[i + 4:close])
            i = close + 1
            continue
        # requires/ensures/... clauses: skip to the body `{` or `;` at depth 0
        # that follows a `,` (Verus clause lists end with a trailing comma).
        if tok in CLAUSES:
            j = i + 1
            while True:
                if t[j] in OPEN and not (t[j] == "{" and t[j - 1] == ","):
                    j = match_close(t, j) + 1
                    continue
                if t[j] == "{" or t[j] == ";":
                    break
                j += 1
            if t[j] == ";":
                j += 1  # trait method declaration ends here; keep a `;`
                out.append(";")
            i = j
            continue
        out.append(tok)
        i += 1
    return normalise_closures(out)


def normalise_closures(t):
    """`|p: T| { e }` and `|p| e` both become `|p| e`, so closure annotations
    the twin needs don't count as changes. Applied to both sides."""
    out = []
    i = 0
    while i < len(t):
        if t[i] == "|" and i > 0 and t[i - 1] in ("(", ",", "move"):
            j = i + 1
            params = []
            while t[j] != "|":
                if t[j] == ":":
                    # skip the type up to `,` or `|` at bracket depth 0
                    k, angle = j + 1, 0
                    while angle or t[k] not in (",", "|"):
                        if t[k] in OPEN:
                            k = match_close(t, k)
                        elif t[k] == "<":
                            angle += 1
                        elif t[k] == ">":
                            angle -= 1
                        k += 1
                    j = k
                    continue
                if t[j] in OPEN:
                    k = match_close(t, j)
                    params.extend(t[j:k + 1])
                    j = k + 1
                    continue
                params.append(t[j])
                j += 1
            out.append("|")
            out.extend(params)
            out.append("|")
            j += 1
            if t[j] == "->":  # return type annotation: always followed by a block
                while t[j] != "{":
                    j += 1
            if t[j] == "{":
                close = match_close(t, j)
                body = normalise_closures(t[j + 1:close])
                out.extend(body)
                i = close + 1
            else:
                i = j
            continue
        out.append(t[i])
        i += 1
    return out


def drop_items(t, names):
    """Remove `fn name ... { }` items (and their attributes/visibility)."""
    out = []
    i = 0
    while i < len(t):
        if t[i] == "fn" and t[i + 1] in names:
            j = i
            while t[j] not in ("{", ";"):
                if t[j] in ("(", "["):
                    j = match_close(t, j)
                j += 1
            if t[j] == "{":  # a definition; trait declarations (`;`) stay
                while out and out[-1] == "pub":
                    out.pop()
                i = match_close(t, j) + 1
                continue
        out.append(t[i])
        i += 1
    return out


def main():
    twin_p, up_p, rw_p = sys.argv[1:4]
    rw = tomllib.loads(open(rw_p).read())
    names = {r["fn"] for r in rw.get("rewrite", [])}
    twin = strip_ghost(open(twin_p).read())
    up = normalise_closures(tokenize(open(up_p).read()))
    for a in rw.get("attribute", []):
        up = " ".join(up).replace(a["upstream"], a["twin"]).split(" ")
    # `#[cfg(test)] mod tests;` is upstream-only.
    up_s = " ".join(up).replace("# [ cfg ( test ) ] mod tests ;", "")
    twin_s = " ".join(drop_items(twin, names))
    up_s = " ".join(drop_items(up_s.split(), names))
    if twin_s == up_s:
        print(f"erasure-check: ok ({len(up_s.split())} tokens; rewrites: {', '.join(sorted(names)) or 'none'})")
        return 0
    a, b = twin_s.split(), up_s.split()
    k = next((n for n in range(min(len(a), len(b))) if a[n] != b[n]), min(len(a), len(b)))
    print("erasure-check: MISMATCH at token", k)
    print("  twin:    ", " ".join(a[max(0, k - 15):k + 15]))
    print("  upstream:", " ".join(b[max(0, k - 15):k + 15]))
    return 1


if __name__ == "__main__":
    sys.exit(main())
