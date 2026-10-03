#!/usr/bin/env bash
# Invoke with bash; executable permission is not required after ZIP extraction.
set -euo pipefail
CODE_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONDONTWRITEBYTECODE=1
exec "${PYTHON:-python3}" "$CODE_DIR/replay.py" "$@"
