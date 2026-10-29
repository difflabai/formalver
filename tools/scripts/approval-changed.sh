#!/usr/bin/env bash
# Has the approval contract changed since the last scheduled check?
#
# Compares trust-framework's default branch to the sha in
# .github/approval-seen, not to the verification pin. The pin stays put
# until a human re-pins, so comparing to it re-ran the proofs every night
# after one upstream move. A change is any file under upstream_path
# (contracts/approval) other than *.md, the same cut trust-framework's
# own CI uses: a doc edit does not change the wasm or the proofs.
#
# Prints contract_changed=true|false and source_ref=<sha-or-empty>.
# When the contract changed, source_ref is the upstream tip to verify.
# When it did not, source_ref is empty and the caller should skip the
# proofs. Also appends those two lines to $GITHUB_OUTPUT when that is set.
#
# Exit 0 if the comparison ran, 2 if it could not.
#
# Local test (no network):
#   approval-changed.sh --repo <git-dir> --pin <sha> --head <sha> --path <path>
#
# CI uses the public upstream without credentials. With GH_TOKEN and
# GITHUB_REPOSITORY set, an open bot PR recording a successful check of the
# same tip also suppresses duplicate runs while its review is pending.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"

emit() {
  printf '%s\n' "$1"
  if [ -n "${GITHUB_OUTPUT:-}" ]; then
    printf '%s\n' "$1" >>"$GITHUB_OUTPUT"
  fi
}

changed_files() {
  # $1 repo, $2 pin, $3 head, $4 path. Prints non-markdown paths, if any.
  git -C "$1" diff --name-only "$2" "$3" -- "$4" | awk '!/\.md$/'
}

if [ "${1:-}" = --repo ]; then
  repo=${2:?} pin=${4:?} head=${6:?} path=${8:?}
  [ "$3" = --pin ] && [ "$5" = --head ] && [ "$7" = --path ] || {
    echo "usage: approval-changed.sh --repo DIR --pin SHA --head SHA --path PATH" >&2
    exit 2
  }
  files=$(changed_files "$repo" "$pin" "$head" "$path")
  if [ -n "$files" ]; then
    echo "Approval contract changed ($pin -> $head):"
    echo "$files"
    emit contract_changed=true
    emit "source_ref=$head"
  else
    echo "Approval contract unchanged ($pin -> $head) under $path, ignoring *.md."
    emit contract_changed=false
    emit source_ref=
  fi
  exit 0
fi

status=projects/near-approval/status.toml
path=$(sed -n 's/^upstream_path = "\([^"]*\)".*/\1/p' "$status")
pin=$(grep -E '^[0-9a-f]{40}$' .github/approval-seen | head -1 || true)
if [ -z "$pin" ]; then
  pin=$(sed -n 's/^pinned_commit = "\([0-9a-f]\{40\}\)".*/\1/p' "$status")
  echo "approval-changed: no .github/approval-seen, falling back to the pin" >&2
fi
[ -n "$pin" ] && [ -n "$path" ] || {
  echo "approval-changed: could not read a baseline sha or upstream_path" >&2
  exit 2
}

url=$(git config -f .gitmodules --get "submodule.projects/near-approval/source-mirror.url")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git init -q "$work"
git -C "$work" remote add origin "$url"
git -C "$work" fetch -q --filter=blob:none origin "$pin" || {
  echo "approval-changed: could not fetch pin $pin from $url" >&2
  exit 2
}
pin_fetch=$(git -C "$work" rev-parse FETCH_HEAD)
git -C "$work" fetch -q --filter=blob:none origin HEAD || {
  echo "approval-changed: could not fetch upstream HEAD from $url" >&2
  exit 2
}
head=$(git -C "$work" rev-parse FETCH_HEAD)

if ! files=$(changed_files "$work" "$pin_fetch" "$head" "$path"); then
  echo "approval-changed: could not compare approval contract revisions" >&2
  exit 2
fi
if [ -n "$files" ]; then
  if [ -n "${GH_TOKEN:-}" ] && [ -n "${GITHUB_REPOSITORY:-}" ]; then
    pr=$(gh pr list --repo "$GITHUB_REPOSITORY" --state open \
      --base "${BASE_BRANCH:-main}" --head "automation/approval-seen-$head" \
      --author 'github-actions[bot]' --json number --jq '.[0].number // empty')
    if [ -n "$pr" ]; then
      echo "Approval contract tip $head already checked; PR #$pr awaits review."
      emit contract_changed=false
      emit source_ref=
      exit 0
    fi
  fi
  {
    echo "### Approval contract changed"
    echo
    echo "Last check \`$pin_fetch\` -> upstream \`$head\`. Verifying \`$head\`."
    echo
    echo '```'
    echo "$files"
    echo '```'
  } >>"${GITHUB_STEP_SUMMARY:-/dev/null}"
  echo "Approval contract changed ($pin_fetch -> $head):"
  echo "$files"
  emit contract_changed=true
  emit "source_ref=$head"
else
  {
    echo "### Approval contract unchanged"
    echo
    echo "\`$path\` at upstream \`$head\` matches the last check \`$pin_fetch\` (ignoring \`*.md\`). Skipping verification."
  } >>"${GITHUB_STEP_SUMMARY:-/dev/null}"
  echo "Approval contract unchanged ($pin_fetch). Skipping verification."
  emit contract_changed=false
  emit source_ref=
fi
