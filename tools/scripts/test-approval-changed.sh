#!/usr/bin/env bash
# Self-test for approval-changed.sh --repo. No network.
set -euo pipefail
script=$(cd "$(dirname "$0")" && pwd)/approval-changed.sh
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git -C "$work" init -q
git -C "$work" config user.email test@example.com
git -C "$work" config user.name test
mkdir -p "$work/contracts/approval/core/src"
printf 'fn a() {}\n' >"$work/contracts/approval/core/src/lib.rs"
printf '# readme\n' >"$work/contracts/approval/README.md"
git -C "$work" add contracts
git -C "$work" commit -q -m pin
pin=$(git -C "$work" rev-parse HEAD)

printf '# readme changed\n' >"$work/contracts/approval/README.md"
git -C "$work" add contracts
git -C "$work" commit -q -m docs
docs=$(git -C "$work" rev-parse HEAD)

out=$("$script" --repo "$work" --pin "$pin" --head "$docs" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=false$' || {
  echo "FAIL: markdown-only change was not ignored" >&2
  echo "$out" >&2
  exit 1
}

printf 'fn b() {}\n' >"$work/contracts/approval/core/src/lib.rs"
git -C "$work" add contracts
git -C "$work" commit -q -m code
code=$(git -C "$work" rev-parse HEAD)
out=$("$script" --repo "$work" --pin "$pin" --head "$code" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=true$' || {
  echo "FAIL: source change was not reported" >&2
  echo "$out" >&2
  exit 1
}
printf '%s\n' "$out" | grep -q "^source_ref=$code$" || {
  echo "FAIL: source_ref was not the upstream tip" >&2
  echo "$out" >&2
  exit 1
}
echo "approval-changed: ok"
