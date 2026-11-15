#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/check-least-bad-eliminate-uniform.sh" "$@"
