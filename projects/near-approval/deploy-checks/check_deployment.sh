#!/usr/bin/env bash
# DEP-1.1-1.5, VER-2, VER-3 and VER-8 (strategy.md section 5.10) for the
# deployment configured in [deployment.<net>] of ../status.toml.
#
#   deploy-checks/check_deployment.sh <net> [--facts FILE] [--json FILE]
#
# Needs python3 >= 3.11 (tomllib) and network access to the net's RPC (an
# archival one on public networks; see check_deployment.py for every key and
# the CHECK_<KEY> environment overrides). Exit 0: no check failed; 1: a check
# failed; 2: configuration error.
set -euo pipefail
exec python3 "$(cd "$(dirname "$0")" && pwd)/check_deployment.py" "$@"
