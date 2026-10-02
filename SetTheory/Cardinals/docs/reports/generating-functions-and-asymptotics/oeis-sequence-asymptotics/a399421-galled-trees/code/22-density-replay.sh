#!/bin/sh
# Location-independent entry point. No downloads or network access are performed.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec "${PYTHON:-python3}" "$SCRIPT_DIR/replay.py" "$@"
