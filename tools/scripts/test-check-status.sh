#!/usr/bin/env bash
# Self-test for check-status.sh: the real status.toml passes, and each kind of
# overclaim fails. The cases edit near-approval's status.toml (read only; the
# edit goes to a scratch copy), the findings cases included: near-approval has
# no [findings], so each adds a [findings.F-T] table and points rows at it.
#
# usage: tools/scripts/test-check-status.sh
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
toml="$here/../../projects/near-approval/status.toml"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0

# expect <0|1> <name> <python edit applied to the file's text>
expect() {
  local want=$1 name=$2 edit=$3
  if ! python3 -I -c "import sys
s=open(sys.argv[1]).read()
$edit
open(sys.argv[2],'w').write(s)" "$toml" "$tmp/s.toml" >"$tmp/out" 2>&1; then
    echo "FAIL: $name: the edit failed"; sed 's/^/  /' "$tmp/out"; fail=1; return
  fi
  STATUS_TOML="$tmp/s.toml" "$here/check-status.sh" near-approval >"$tmp/out" 2>&1
  local got=$?
  [ "$got" -gt 1 ] && got=2
  if [ "$got" != "$want" ]; then
    echo "FAIL: $name: exit $got, want $want"; sed 's/^/  /' "$tmp/out"; fail=1
  fi
}

expect 0 "current status.toml" "pass"
# A Kani property at verified-with-assumptions with no spec reviewer.
expect 1 "K property past in-progress without sign-off" \
  "import re; s=re.sub(r'(ROB-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified-with-assumptions\"', s, count=1)"
# ...and above the Kani ceiling even with a reviewer.
expect 1 "Kani at verified" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(ROB-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified\"', s, count=1)"
# Sign-off present: verified-with-assumptions is fine.
expect 0 "K property with sign-off" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(ROB-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified-with-assumptions\"', s, count=1)"
# Evidence a layer can't give.
expect 1 "evidence not allowed for layer" \
  "import re; s=re.sub(r'(ROB-1 = \{[^}]*evidence = )\"bounded-proof\"', r'\1\"proof\"', s, count=1)"
# Verus path A: `verified` only with no assumptions left.
expect 1 "Verus verified with assumptions" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(TX-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified\"', s, count=1)"
expect 0 "Verus verified-with-assumptions with sign-off" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(TX-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified-with-assumptions\"', s, count=1)"
# A property claimed with no artifact behind it.
expect 1 "claimed without PROP tag" \
  "import re; s=s.replace('[modules.requirements.properties]', '[modules.requirements.properties]\n  ZZ-1 = { status = \"in-progress\", layer = \"kani\", evidence = \"bounded-proof\", description = \"x\" }', 1)"

# Findings (plan-meta section 4). fnd adds [findings.<fid>]; key adds a key
# to a property's inline table. ROB-1 and TX-1 are in-progress rows;
# ASM-SIGNER is an assumption.
H='import json, re
def fnd(status, by, closed_in="v1.1.0", fid="F-T"):
    global s
    body = "status = %s\nclosed_by = %s\n" % (json.dumps(status), json.dumps(by))
    if closed_in:
        body += "closed_in = %s\n" % json.dumps(closed_in)
    s = s.rstrip("\n") + "\n\n[findings.%s]\n" % fid + body
def key(pid, k, v):
    global s
    a = "  " + pid + " = { "
    assert s.count(a) == 1, pid
    s = s.replace(a, a + k + " = " + json.dumps(v) + ", ")
'
expect 0 "finding closed by an in-progress row" \
  "$H"'key("ROB-1", "closes", ["F-T"]); fnd("closed", ["ROB-1"])'
expect 0 "closed_by may also name an assumption" \
  "$H"'key("ROB-1", "closes", ["F-T"]); fnd("closed", ["ROB-1", "ASM-SIGNER"])'
expect 1 "closes names no [findings] table" \
  "$H"'key("ROB-1", "closes", ["F-T", "F-X"]); fnd("closed", ["ROB-1"])'
expect 1 "closes without any [findings]" \
  "$H"'key("ROB-1", "closes", ["F-T"])'
expect 1 "closed_by names an unknown ID" \
  "$H"'key("ROB-1", "closes", ["F-T"]); fnd("closed", ["ROB-1", "ZZ-9"])'
expect 1 "closed_by lists a row whose closes omits the finding" \
  "$H"'fnd("closed", ["ROB-1"])'
expect 1 "closes not echoed in closed_by" \
  "$H"'key("ROB-1", "closes", ["F-T"]); key("TX-1", "closes", ["F-T"]); fnd("closed", ["TX-1"])'
expect 1 "closed with every closer at rank 0" \
  "$H"'s = s.replace("  ROB-1 = { status = \"in-progress\"", "  ROB-1 = { status = \"unverified\"", 1); key("ROB-1", "closes", ["F-T"]); fnd("closed", ["ROB-1"])'
expect 1 "closed with an empty closed_by" \
  "$H"'fnd("closed", [])'
expect 1 "closed without closed_in" \
  "$H"'key("ROB-1", "closes", ["F-T"]); fnd("closed", ["ROB-1"], closed_in="")'
expect 0 "rejected with an empty closed_by" \
  "$H"'fnd("rejected", [], closed_in="")'
expect 1 "unknown finding status" \
  "$H"'fnd("fixed", [], closed_in="")'
expect 0 "finding names an open finding" \
  "$H"'key("TX-1", "finding", "F-T"); fnd("open", [], closed_in="")'
expect 1 "finding names a closed finding" \
  "$H"'key("ROB-1", "closes", ["F-T"]); key("TX-1", "finding", "F-T"); fnd("closed", ["ROB-1"])'
expect 1 "finding names no [findings] table" \
  "$H"'key("TX-1", "finding", "F-T, F-X"); fnd("open", [], closed_in="")'

if [ "$fail" = 0 ]; then echo "check-status self-test ok"; fi
exit "$fail"
