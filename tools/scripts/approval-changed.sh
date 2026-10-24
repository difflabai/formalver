#!/usr/bin/env bash
# Has the approval contract changed since the pin?
#
# Compares trust-framework's default branch to pinned_commit in
# projects/near-approval/status.toml. A change is any file under
# upstream_path (contracts/approval) other than *.md, the same cut
# trust-framework's own CI uses: a doc edit does not change the wasm
# or the proofs.
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
# CI: CROSS_REPO_BUILD_KEY if the upstream is still private (token or SSH
# deploy key), same rewrite as ci-submodule.sh.
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
pin=$(sed -n 's/^pinned_commit = "\([0-9a-f]\{40\}\)".*/\1/p' "$status")
path=$(sed -n 's/^upstream_path = "\([^"]*\)".*/\1/p' "$status")
[ -n "$pin" ] && [ -n "$path" ] || {
  echo "approval-changed: could not read pinned_commit or upstream_path from $status" >&2
  exit 2
}

url=$(git config -f .gitmodules --get "submodule.projects/near-approval/source-mirror.url")
repo=${url#https://github.com/}
repo=${repo%.git}
key=${CROSS_REPO_BUILD_KEY:-}

known_hosts=
if [ -n "$key" ]; then
  if [[ $key == -----BEGIN* ]]; then
    eval "$(ssh-agent -s)" >/dev/null
    known_hosts=$(mktemp)
    ssh-add - <<<"$key" 2>/dev/null
    ssh-keyscan -t ed25519 github.com >"$known_hosts" 2>/dev/null
    export GIT_SSH_COMMAND="ssh -o UserKnownHostsFile=$known_hosts"
    rewrite="git@github.com:$repo"
  else
    echo "::add-mask::$key"
    rewrite="https://x-access-token:$key@github.com/$repo"
  fi
  export GIT_CONFIG_COUNT=2
  export GIT_CONFIG_KEY_0="url.$rewrite.insteadOf"
  export GIT_CONFIG_VALUE_0="https://github.com/$repo"
  export GIT_CONFIG_KEY_1=credential.helper
  export GIT_CONFIG_VALUE_1=
fi

work=$(mktemp -d)
trap 'rm -rf "$work"; rm -f "$known_hosts"; ssh-agent -k >/dev/null 2>&1 || true' EXIT
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

files=$(changed_files "$work" "$pin_fetch" "$head" "$path" || true)
if [ -n "$files" ]; then
  {
    echo "### Approval contract changed"
    echo
    echo "Pin \`$pin_fetch\` -> upstream \`$head\`. Verifying \`$head\`, not the pin."
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
    echo "\`$path\` at upstream \`$head\` matches pin \`$pin_fetch\` (ignoring \`*.md\`). Skipping verification."
  } >>"${GITHUB_STEP_SUMMARY:-/dev/null}"
  echo "Approval contract unchanged ($pin_fetch). Skipping verification."
  emit contract_changed=false
  emit source_ref=
fi
