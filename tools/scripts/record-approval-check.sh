#!/usr/bin/env bash
# After successful scheduled verification, propose its upstream baseline in
# a PR. Never push main or change the human-reviewed verification pin.
# Run in a fresh checkout of the current default branch.
set -euo pipefail

seen=${1:?usage: record-approval-check.sh <verified upstream sha>}
[[ $seen =~ ^[0-9a-f]{40}$ ]] || { echo 'invalid upstream sha' >&2; exit 2; }
: "${GH_TOKEN:?GH_TOKEN is required}"
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"
: "${GITHUB_RUN_ID:?GITHUB_RUN_ID is required}"
base=${BASE_BRANCH:-main}
branch="automation/approval-seen-$seen"

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo 'record-approval-check: checkout must be clean' >&2; exit 2
fi
current=$(grep -E '^[0-9a-f]{40}$' .github/approval-seen | head -1 || true)
if [ "$current" = "$seen" ]; then
  echo "Approval contract tip $seen is already recorded."
  exit 0
fi
pr=$(gh pr list --repo "$GITHUB_REPOSITORY" --state open --base "$base" \
  --head "$branch" --author 'github-actions[bot]' --json number --jq '.[0].number // empty')
if [ -n "$pr" ]; then
  echo "Approval check already proposed in PR #$pr."
  exit 0
fi

printf '%s\n' \
  '# Upstream tip successfully checked by the scheduled near-approval run.' \
  '# Not the verification pin. The pin stays until a human re-pins.' \
  "$seen" > .github/approval-seen
git add -- .github/approval-seen
git -c user.email='github-actions[bot]@users.noreply.github.com' \
    -c user.name='github-actions[bot]' -c commit.gpgsign=false \
    commit -m "ci: record successful approval check at $seen"

# Only this SHA-specific automation branch may be replaced. The lease
# refuses to overwrite work added since we checked it; main is never a target.
expected=$(git ls-remote origin "refs/heads/$branch" | cut -f1)
git -c credential.helper= \
    -c "http.https://github.com/.extraheader=AUTHORIZATION: bearer $GH_TOKEN" \
    push --force-with-lease="refs/heads/$branch:$expected" origin "HEAD:refs/heads/$branch"

body=$(mktemp)
trap 'rm -f "$body"' EXIT
cat >"$body" <<EOF
Scheduled verification succeeded for trust-framework upstream tip \`$seen\`.

The schedule compared non-Markdown files under \`contracts/approval\` against
\`.github/approval-seen\` and verified the changed upstream tip before opening
this PR. Merge to advance that baseline and avoid duplicate nightly checks.
The verification pin and its reviewed source hashes are unchanged.

Verification run: ${GITHUB_SERVER_URL:-https://github.com}/$GITHUB_REPOSITORY/actions/runs/${GITHUB_RUN_ID:?GITHUB_RUN_ID is required}
EOF
gh pr create --repo "$GITHUB_REPOSITORY" --base "$base" --head "$branch" \
  --title "ci: record approval check at ${seen:0:12}" --body-file "$body"
