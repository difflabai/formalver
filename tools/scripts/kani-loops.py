#!/usr/bin/env python3
"""U-1: derive the unwind bound of every loop in every Kani harness.

Lists each harness's loops from its goto program (goto-instrument
--show-loops) and gives each one a bound derived from the code, instead of
the one global #[kani::unwind(n)]:

  * loops in the harness crate: parsed from the loop header
    (`for i in 0..CAP_P`, `while i < pre.nr`, `while k < NK`, ...), with
    counts (`np`, `nr`, `nl`, `nv`) bounded by their store capacity, which
    ArrStore's push_* asserts (U-2);
  * library loops: by the rules in <crate>/unwind-rules.tsv, each with its
    reason.

A loop with no derivable bound is an error. The bound is the CBMC unwind
count: iterations + 1.

usage: kani-loops.py <crate-dir> [--codegen] [--harness H ...] [--unwindset H]
  --codegen      run `cargo kani --only-codegen --keep-temps` first
  --harness H    only these harnesses (default: all with a goto program)
  --unwindset H  print the --unwindset argument for harness H and exit
  --core-file F  the verified library source; any loop in it must be listed
                 in the rules (default: none allowed)

Report columns: harness, unwind attribute, loop id, location, bound, rule.
Exit 1 if a loop has no bound, or a loop of the verified library is not
covered by a rule. Bounds above a harness's #[kani::unwind] are listed as
"needs N > unwind M": they are where an unwinding assertion can fail.
The listing is static: a flagged loop in code a harness never reaches (a
branch on a constant, such as checks.rs's `part`) cannot fail, and is
checked by hand (kani/RESULTS.md, "Loop bounds").
"""
import argparse
import glob
import os
import re
import shutil
import subprocess
import sys


def consts(paths):
    """`const NAME: T = <int or NAME>;` across the given files."""
    raw = {}
    for p in paths:
        for m in re.finditer(r"const\s+([A-Z_][A-Z0-9_]*)\s*:\s*[\w:]+\s*=\s*([^;]+);", open(p).read()):
            raw[m.group(1)] = m.group(2).strip()
    out = {}

    def val(n, seen=()):
        if n in out:
            return out[n]
        v = raw.get(n)
        if v is None or n in seen:
            return None
        v = v.replace("_", "") if re.fullmatch(r"[\d_]+", v) else v
        if re.fullmatch(r"\d+", v):
            out[n] = int(v)
        elif re.fullmatch(r"[A-Z_][A-Z0-9_]*", v):
            r = val(v, seen + (n,))
            if r is not None:
                out[n] = r
        return out.get(n)

    for n in raw:
        val(n)
    # Array constants: `NAME: [T; n]` gives NAME_LEN; `NAME: [[T; m]; n]`
    # also NAME_INNER = m.
    for p in paths:
        src = open(p).read()
        for m in re.finditer(r"const\s+([A-Z_][A-Z0-9_]*)\s*:\s*\[\[[^;\]]+;\s*(\d+)\];\s*(\d+)\]", src):
            out.setdefault(m.group(1) + "_INNER", int(m.group(2)))
            out.setdefault(m.group(1) + "_LEN", int(m.group(3)))
        for m in re.finditer(r"const\s+([A-Z_][A-Z0-9_]*)\s*:\s*\[[^;\[\]]+;\s*(\d+)\]", src):
            out.setdefault(m.group(1) + "_LEN", int(m.group(2)))
    return out


def evaluate(expr, env):
    expr = expr.strip()
    toks = re.split(r"(\W)", expr)
    py = "".join(str(env[t]) if t in env else t for t in toks)
    if not re.fullmatch(r"[\d\s+\-*()]+", py):
        raise ValueError(f"cannot evaluate {expr!r} -> {py!r}")
    return eval(py)  # digits and + - * ( ) only


# Loop counts in harness code and the capacity that bounds each (U-2:
# ArrStore::push_* assert the capacity; snap() copies at most that many).
COUNTS = {"np": "CAP_P", "nr": "CAP_R", "nl": "CAP_R", "nv": "CAP_V", "n": "CR"}

# Other loop limits in harness code, by their exact text.
ALIASES = {
    "end": "CAP_R",  # checks::page_exact: end <= #L <= CAP_R
    "page.len()": "CAP_R",  # a page holds at most #L proofs
    "depth": "MAX_DEPTH",  # checks::trace: depth <= MAX_DEPTH
    "ACTIONS.len()": "ACTIONS_LEN",
}


def crate_bound(line, fn, env):
    """Bound of a loop in the harness crate from its header, or None."""
    m = re.search(r"for\s+\w+\s+in\s+(\w+)\.\.(\w+)", line)
    if m:
        lo, hi = evaluate(m.group(1), env), evaluate(m.group(2), env)
        return max(hi - lo, 0) + 1, f"for {m.group(1)}..{m.group(2)}"
    m = re.search(r"while\s+\w+(\s*\+\s*1)?\s*<\s*([\w.():]+?)(?:\s+as\s+\w+)?\s*\{", line)
    if m:
        lim = m.group(2)
        plus = 1 if m.group(1) else 0
        name = re.split(r"\.|::", re.sub(r"\(\)$", "", lim))[-1]
        if lim == "C":  # const generic: read it from the instance name
            g = re.search(r"::<(\d+)>", fn)
            if not g:
                return None
            return int(g.group(1)) - plus + 1, "while < C (const generic)"
        if name in env:
            return env[name] - plus + 1, f"while < {name}"
        if name in COUNTS:
            cap = COUNTS[name]
            return env[cap] - plus + 1, f"while < {lim} <= {cap}"
        if lim in ALIASES:
            a = ALIASES[lim]
            return env[a] - plus + 1, f"while < {lim} <= {a}"
        return None
    m = re.search(r"for\s+.+\s+in\s+\w+\.(principals|requests)\(\)\.iter\(\)", line)
    if m:
        cap = {"principals": "CAP_P", "requests": "CAP_R"}[m.group(1)]
        return env[cap] + 1, f"{m.group(1)}() <= {cap}"
    return None


def rules(path):
    out = []
    for ln in open(path):
        ln = ln.rstrip("\n")
        if not ln.strip() or ln.lstrip().startswith("#"):
            continue
        pat, bound, why = (ln.split("\t") + ["", ""])[:3]
        out.append((re.compile(pat), bound, why))
    return out


def unwind_attrs(proofs):
    """#[kani::unwind(n)] per harness name in proofs.rs (macro parts too)."""
    src = open(proofs).read()
    out = {}
    for m in re.finditer(r"#\[kani::unwind\((\d+)\)\]\s*fn\s+(\w+)", src):
        out[m.group(2)] = int(m.group(1))
    # step_parts!: every generated part has the macro's unwind
    mm = re.search(r"macro_rules!\s*step_parts.*?#\[kani::unwind\((\d+)\)\]", src, re.S)
    if mm:
        for m in re.finditer(r"\b(h_step_\w+_(?:tx|post|hist|inv|reg))\b", src):
            out.setdefault(m.group(1), int(mm.group(1)))
    return out


def goto_files(crate):
    """Newest goto program per harness."""
    best = {}
    for f in glob.glob(os.path.join(crate, "target/kani/*/debug/build/*/*/out/*.out")):
        if f.endswith(".symtab.out"):
            continue
        m = re.search(r"proofs\d*(h_\w+)\.out$", os.path.basename(f))
        if not m:
            continue
        h = m.group(1)
        if h not in best or os.path.getmtime(f) > os.path.getmtime(best[h]):
            best[h] = f
    return best


def loops(gi, f):
    out = subprocess.run([gi, "--show-loops", f], capture_output=True, text=True, check=True).stdout
    cur = None
    for ln in out.splitlines():
        m = re.match(r"Loop (\S+):$", ln)
        if m:
            cur = m.group(1)
            continue
        m = re.match(r"\s+file (\S+) line (\d+) column \d+ function (.*)$", ln)
        if m and cur:
            yield cur, m.group(1), int(m.group(2)), m.group(3)
            cur = None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("--codegen", action="store_true")
    ap.add_argument("--harness", nargs="*")
    ap.add_argument("--unwindset")
    ap.add_argument("--core-file", default="")
    a = ap.parse_args()
    crate = os.path.abspath(a.crate)
    if a.codegen:
        subprocess.run(["cargo", "kani", "--only-codegen", "--keep-temps"], cwd=crate, check=True)
    kani_home = os.environ.get("KANI_HOME") or os.path.expanduser("~/.kani")
    kani_dirs = sorted(glob.glob(os.path.join(kani_home, "kani-*/bin")))
    gi = shutil.which("goto-instrument") or (kani_dirs and os.path.join(kani_dirs[-1], "goto-instrument"))
    if not gi or not os.path.exists(gi):
        sys.exit("goto-instrument not found (install Kani)")

    srcs = glob.glob(os.path.join(crate, "src/*.rs"))
    extra = [a.core_file] if a.core_file else []
    env = consts(srcs + extra)
    rule_file = os.path.join(crate, "unwind-rules.tsv")
    rs = rules(rule_file) if os.path.exists(rule_file) else []
    attrs = unwind_attrs(os.path.join(crate, "src/proofs.rs"))
    files = goto_files(crate)
    hs = [a.unwindset] if a.unwindset else (a.harness or sorted(files))

    bad = 0
    lines = []
    for h in hs:
        if h not in files:
            print(f"{h}: no goto program (run with --codegen)", file=sys.stderr)
            bad = 1
            continue
        uw = attrs.get(h)
        sets = []
        for lid, path, line, fn in loops(gi, files[h]):
            loc = f"{path}:{line} {fn}"
            bound, why = None, None
            local = os.path.join(crate, path)
            if not os.path.isabs(path) and os.path.exists(local):
                text = open(local).read().splitlines()[line - 1]
                try:
                    r = crate_bound(text, fn, env)
                except (ValueError, KeyError) as e:
                    r = None
                    why = f"header not derivable: {e}"
                if r:
                    bound, why = r
                else:
                    why = why or f"header not derivable: {text.strip()}"
            if bound is None:
                for pat, b, w in rs:
                    if pat.search(loc):
                        if b == "core-loop-forbidden":
                            bound, why = None, f"loop in the verified library: {w}"
                        else:
                            bound, why = evaluate(b, env), f"rule: {w}"
                        break
            if a.core_file and os.path.abspath(path) == os.path.abspath(a.core_file) and not why.startswith("rule"):
                bound, why = None, "loop in the verified library not covered by a rule"
            if bound is None:
                bad = 1
                lines.append((h, uw, lid, loc, "NONE", why))
                continue
            sets.append(f"{lid}:{bound}")
            flag = f"needs {bound} > unwind {uw}" if uw is not None and bound > uw else ""
            lines.append((h, uw, lid, loc, bound, why + (f"; {flag}" if flag else "")))
        if a.unwindset:
            print(",".join(sets))
            return bad
    for ln in lines:
        print("\t".join(str(x) for x in ln))
    return bad


if __name__ == "__main__":
    sys.exit(main())
