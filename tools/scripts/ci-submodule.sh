#!/usr/bin/env bash
# CI only: checks out one private submodule with CROSS_REPO_BUILD_KEY, which
# may be a token (PAT or app token) or an SSH deploy key. Other submodules
# stay uninitialised.
#
# The URL rewrite is passed to git through GIT_CONFIG_COUNT (inherited by the
# submodule clone), and the SSH agent and known_hosts live only as long as
# this script, not in ~/.gitconfig or ~/.ssh: a self-hosted runner keeps HOME
# between jobs, and other repositories' jobs run on it. Credential helpers
# are switched off so none (e.g. macOS's osxkeychain, set in git's system
# config) stores the token.
#
# usage: tools/scripts/ci-submodule.sh <submodule path>
set -euo pipefail
path=${1:?usage: ci-submodule.sh <submodule path>}
key=${CROSS_REPO_BUILD_KEY:?CROSS_REPO_BUILD_KEY is not set}
url=$(git config -f .gitmodules --get "submodule.$path.url")
repo=${url#https://github.com/}
repo=${repo%.git}

if [[ $key == -----BEGIN* ]]; then
  eval "$(ssh-agent -s)" >/dev/null
  known_hosts=$(mktemp)
  trap 'ssh-agent -k >/dev/null 2>&1 || true; rm -f "$known_hosts"' EXIT
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
git submodule update --init --depth 1 -- "$path"
