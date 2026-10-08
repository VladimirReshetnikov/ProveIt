#!/bin/sh
# Run the complete integrated Python suite, independent of the caller's cwd.
set -eu
bundle_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
PYTHONPATH="$bundle_root/fast${PYTHONPATH:+:$PYTHONPATH}"
export PYTHONPATH
cd "$bundle_root"
exec "${TWIST_PYTHON:-python3}" -m unittest discover -s "$bundle_root/fast/tests" -v
