#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/check-bad-inside-eliminate-uniform.sh" "$@"
