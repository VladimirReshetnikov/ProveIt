#!/bin/sh
# No source payload code runs until verify_release.py has checked the entire tree.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON=${PYTHON:-python3}
exec "$PYTHON" -I -B "$ROOT/verify_release.py" --replay
