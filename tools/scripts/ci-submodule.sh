#!/usr/bin/env bash
# CI only: checks out one private submodule with CROSS_REPO_BUILD_KEY, which
# may be a token (PAT or app token) or an SSH deploy key. Other submodules
# stay uninitialised.
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
  ssh-add - <<<"$key" 2>/dev/null
  mkdir -p ~/.ssh && ssh-keyscan -t ed25519 github.com >>~/.ssh/known_hosts 2>/dev/null
  git config --global url."git@github.com:$repo".insteadOf "https://github.com/$repo"
else
  echo "::add-mask::$key"
  git config --global url."https://x-access-token:$key@github.com/$repo".insteadOf "https://github.com/$repo"
fi
git submodule update --init --depth 1 -- "$path"
