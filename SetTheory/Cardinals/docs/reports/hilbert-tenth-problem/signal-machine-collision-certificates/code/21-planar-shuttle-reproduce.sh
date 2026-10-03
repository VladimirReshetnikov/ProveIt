#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if test "$#" -ne 1; then echo 'Usage: ./reproduce.sh /absolute/external/empty-output-directory' >&2; exit 2; fi
exec python3 -I -B "$ROOT/replay.py" --output-dir "$1"
