#!/usr/bin/env bash
# Verify whole push/PR ranges rather than just the most recent commit.
set -euo pipefail
script=$(cd "$(dirname "$0")" && pwd)/ci-changed-areas.sh
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git -C "$work" init -q
git -C "$work" config user.name test
git -C "$work" config user.email test@example.com
git -C "$work" config commit.gpgsign false
mkdir -p "$work/projects/near-approval/prolog/requirements"
printf 'initial\n' > "$work/README.md"
git -C "$work" add .
git -C "$work" commit -qm base
base=$(git -C "$work" rev-parse HEAD)
printf 'rule.\n' > "$work/projects/near-approval/prolog/requirements/r.pl"
git -C "$work" add .
git -C "$work" commit -qm prolog
prolog=$(git -C "$work" rev-parse HEAD)
printf 'docs\n' >> "$work/README.md"
git -C "$work" add .
git -C "$work" commit -qm docs
cd "$work"
selected() { "$script" | sed -n 's/=true$//p' | tr '\n' ' ' | sed 's/ $//'; }
export SOURCE_REF=''
out=$(GITHUB_EVENT_NAME=push BASE_SHA="$base" selected 2>"$work/explain.log")
[ "$out" = prolog ] || { echo "FAIL: multi-commit push -> $out" >&2; exit 1; }
out=$(GITHUB_EVENT_NAME=pull_request BASE_SHA="$prolog" selected 2>"$work/explain.log")
[ -z "$out" ] || { echo "FAIL: docs-only PR -> $out" >&2; exit 1; }
out=$(GITHUB_EVENT_NAME=pull_request BASE_SHA="$base" selected 2>"$work/explain.log")
[ "$out" = prolog ]
out=$(GITHUB_EVENT_NAME=push BASE_SHA=0000000000000000000000000000000000000000 selected)
[ "$out" = 'plain loops kani tla lean prolog near_unit sandbox verus' ]
out=$(GITHUB_EVENT_NAME=schedule selected)
[ "$out" = 'plain loops kani tla lean prolog near_unit sandbox verus' ]
out=$(GITHUB_EVENT_NAME=push SOURCE_REF=1111111111111111111111111111111111111111 selected)
[ "$out" = 'plain loops kani tla lean prolog near_unit sandbox verus' ]
before_rename=$(git rev-parse HEAD)
mkdir -p projects/near-approval/lean
git mv projects/near-approval/prolog/requirements/r.pl projects/near-approval/lean/Rule.lean
git commit -qm rename-layer
out=$(GITHUB_EVENT_NAME=push BASE_SHA="$before_rename" selected 2>"$work/explain.log")
[ "$out" = 'lean prolog' ] || { echo "FAIL: renamed layer -> $out" >&2; exit 1; }
echo 'ci-changed-areas: all cases pass'
