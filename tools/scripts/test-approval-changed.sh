#!/usr/bin/env bash
# Self-test for approval-changed.sh --repo. No network.
set -euo pipefail
script=$(cd "$(dirname "$0")" && pwd)/approval-changed.sh
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git -C "$work" init -q
git -C "$work" config user.email test@example.com
git -C "$work" config user.name test
git -C "$work" config commit.gpgsign false
mkdir -p "$work/contracts/approval/core/src"
printf 'fn a() {}\n' >"$work/contracts/approval/core/src/lib.rs"
printf '# readme\n' >"$work/contracts/approval/README.md"
git -C "$work" add contracts
git -C "$work" commit -q -m pin
pin=$(git -C "$work" rev-parse HEAD)

# Changes elsewhere in trust-framework must not schedule approval proofs.
printf 'unrelated\n' >"$work/other.txt"
git -C "$work" add other.txt
git -C "$work" commit -q -m unrelated
other=$(git -C "$work" rev-parse HEAD)
out=$("$script" --repo "$work" --pin "$pin" --head "$other" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=false$'

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

# Once the baseline advances to the checked tip, the same code is skipped.
out=$("$script" --repo "$work" --pin "$code" --head "$code" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=false$'

# Dependency changes and deletions inside the approval directory count too.
printf 'lockfile\n' >"$work/contracts/approval/Cargo.lock"
git -C "$work" add contracts
git -C "$work" commit -q -m dependencies
deps=$(git -C "$work" rev-parse HEAD)
out=$("$script" --repo "$work" --pin "$code" --head "$deps" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=true$'
git -C "$work" rm -q contracts/approval/core/src/lib.rs
git -C "$work" commit -q -m deletion
deleted=$(git -C "$work" rev-parse HEAD)
out=$("$script" --repo "$work" --pin "$deps" --head "$deleted" --path contracts/approval)
printf '%s\n' "$out" | grep -q '^contract_changed=true$'

# Git comparison errors must fail; they must never be reported as unchanged.
if "$script" --repo "$work" --pin 0000000000000000000000000000000000000000 \
    --head "$code" --path contracts/approval >"$work/error.log" 2>&1; then
  echo 'FAIL: comparison failure was ignored' >&2; exit 1
fi

# Exercise the CI path with a local upstream and a mocked GitHub API. This
# verifies pending PR suppression and API failures without network access.
ci="$work/ci"
mkdir -p "$ci/tools/scripts" "$ci/.github" "$ci/projects/near-approval" "$ci/bin"
cp "$script" "$ci/tools/scripts/approval-changed.sh"
printf '%s\n' "$pin" > "$ci/.github/approval-seen"
printf 'upstream_path = "contracts/approval"\n' > "$ci/projects/near-approval/status.toml"
git config -f "$ci/.gitmodules" submodule.projects/near-approval/source-mirror.url "$work"
cat > "$ci/bin/gh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [ "${PR_TEST_FAIL:-}" = 1 ]; then exit 19; fi
printf '%s' "${EXISTING_PR:-}"
SH
chmod +x "$ci/bin/gh"
export PATH="$ci/bin:$PATH" GH_TOKEN=test GITHUB_REPOSITORY=example/formalver
out=$(EXISTING_PR=42 "$ci/tools/scripts/approval-changed.sh" 2>"$work/fetch.log")
printf '%s\n' "$out" | grep -q '^contract_changed=false$'
out=$(EXISTING_PR='' "$ci/tools/scripts/approval-changed.sh" 2>"$work/fetch.log")
printf '%s\n' "$out" | grep -q '^contract_changed=true$'
printf '%s\n' "$out" | grep -q "^source_ref=$deleted$"
if PR_TEST_FAIL=1 "$ci/tools/scripts/approval-changed.sh" >"$work/api-error.log" 2>&1; then
  echo 'FAIL: GitHub API failure was ignored' >&2; exit 1
fi
echo "approval-changed: ok"
