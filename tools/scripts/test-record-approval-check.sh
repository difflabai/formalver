#!/usr/bin/env bash
# Exercise the real Git commit/push against a local bare remote; mock only
# the GitHub PR API. No network, credentials, or changes to the workspace.
set -euo pipefail
script=$(cd "$(dirname "$0")" && pwd)/record-approval-check.sh
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git init -q --bare "$work/remote.git"
git init -q -b main "$work/repo"
git -C "$work/repo" config user.name test
git -C "$work/repo" config user.email test@example.com
git -C "$work/repo" config commit.gpgsign false
mkdir -p "$work/repo/.github" "$work/bin"
old=1111111111111111111111111111111111111111
seen=2222222222222222222222222222222222222222
printf '%s\n' "$old" > "$work/repo/.github/approval-seen"
printf 'unchanged pin\n' > "$work/repo/status.toml"
git -C "$work/repo" add .
git -C "$work/repo" commit -qm initial
git -C "$work/repo" remote add origin "$work/remote.git"
git -C "$work/repo" push -q origin main
base=$(git -C "$work/repo" rev-parse HEAD)
cat > "$work/bin/gh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
case "$1 $2" in
  'pr list') printf '%s' "${EXISTING_PR:-}" ;;
  'pr create')
    while [ "$#" -gt 0 ]; do
      if [ "$1" = --body-file ]; then cp "$2" "$PR_TEST_STATE/body.md"; fi
      shift
    done
    echo created >> "$PR_TEST_STATE/created"
    ;;
  *) echo 'unexpected gh command' >&2; exit 2 ;;
esac
SH
chmod +x "$work/bin/gh"
export PATH="$work/bin:$PATH" PR_TEST_STATE="$work"
export GH_TOKEN=test GITHUB_REPOSITORY=example/formalver GITHUB_RUN_ID=123 BASE_BRANCH=main
cd "$work/repo"

if "$script" 'not-a-sha' >"$work/invalid.log" 2>&1; then
  echo 'FAIL: invalid SHA accepted' >&2; exit 1
fi
"$script" "$seen" >"$work/record.log" 2>&1
branch="refs/heads/automation/approval-seen-$seen"
[ "$(git --git-dir="$work/remote.git" rev-parse refs/heads/main)" = "$base" ]
[ "$(git --git-dir="$work/remote.git" show "$branch:.github/approval-seen" | tail -1)" = "$seen" ]
[ "$(git diff --name-only "$base" HEAD)" = .github/approval-seen ]
grep -q "$seen" "$work/body.md"
grep -q '/actions/runs/123' "$work/body.md"
[ "$(wc -l < "$work/created" | tr -d ' ')" = 1 ]

# Retrying after the baseline merged makes no commit or PR.
tip=$(git rev-parse HEAD)
"$script" "$seen" >"$work/already.log" 2>&1
[ "$(git rev-parse HEAD)" = "$tip" ]
[ "$(wc -l < "$work/created" | tr -d ' ')" = 1 ]

# Before merge, an existing proposal also makes a repeat a no-op.
git checkout -q --detach "$base"
EXISTING_PR=42 "$script" "$seen" >"$work/pending.log" 2>&1
[ "$(git rev-parse HEAD)" = "$base" ]
[ "$(wc -l < "$work/created" | tr -d ' ')" = 1 ]
echo 'record-approval-check: all cases pass'
