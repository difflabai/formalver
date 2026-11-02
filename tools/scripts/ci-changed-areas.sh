#!/usr/bin/env bash
# Select verification jobs from the complete PR/push diff. An upstream
# verification call or manual run checks all layers. Missing Git history
# conservatively runs all layers rather than silently missing a change.
set -euo pipefail
areas=$(cd "$(dirname "$0")" && pwd)/ci-areas.sh
if [ -n "${SOURCE_REF:-}" ]; then
  [[ $SOURCE_REF =~ ^[0-9a-f]{40}$ ]] || { echo 'invalid upstream ref' >&2; exit 2; }
  "$areas" --all </dev/null
  exit 0
fi
case "${GITHUB_EVENT_NAME:-}" in
  pull_request | push)
    base=${BASE_SHA:-}
    if [[ $base =~ ^[0-9a-f]{40}$ ]] && [[ $base != 0000000000000000000000000000000000000000 ]]; then
      if git cat-file -e "$base^{commit}" 2>/dev/null || git fetch --no-tags --depth 1 origin "$base"; then
        git diff --no-renames --name-only "$base" HEAD | CI_AREAS_EXPLAIN=1 "$areas"
        exit 0
      fi
    fi
    echo 'CI base unavailable; checking every verification layer.' >&2
    ;;
esac
"$areas" --all </dev/null
