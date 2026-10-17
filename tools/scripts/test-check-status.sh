#!/usr/bin/env bash
# Self-test for check-status.sh: the real status.toml passes, and each kind of
# overclaim fails.
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
  python3 -I -c "import sys; s=open(sys.argv[1]).read(); $edit; open(sys.argv[2],'w').write(s)" "$toml" "$tmp/s.toml"
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
  "import re; s=re.sub(r'(TX-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified-with-assumptions\"', s, count=1)"
# ...and above the Kani ceiling even with a reviewer.
expect 1 "Kani at verified" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(TX-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified\"', s, count=1)"
# Sign-off present: verified-with-assumptions is fine.
expect 0 "K property with sign-off" \
  "import re; s=re.sub(r'spec_reviewer = \"\"', 'spec_reviewer = \"someone\"', s, count=1); s=re.sub(r'(TX-1 = \{ status = )\"[a-z-]+\"', r'\1\"verified-with-assumptions\"', s, count=1)"
# Evidence a layer can't give.
expect 1 "evidence not allowed for layer" \
  "import re; s=re.sub(r'(TX-1 = \{[^}]*evidence = )\"bounded-proof\"', r'\1\"proof\"', s, count=1)"
# A property claimed with no artifact behind it.
expect 1 "claimed without PROP tag" \
  "import re; s=s.replace('[modules.requirements.properties]', '[modules.requirements.properties]\n  ZZ-1 = { status = \"in-progress\", layer = \"kani\", evidence = \"bounded-proof\", description = \"x\" }', 1)"

if [ "$fail" = 0 ]; then echo "check-status self-test ok"; fi
exit "$fail"
