#!/usr/bin/env bash
# Compile the modules of this directory with every standalone module they import, through
# ../pa194-model-fairness/check_bridge.py. Arguments are passed on (for example --out DIR to
# reuse compiled objects).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194SemanticNeighborhoodExact.lean" --reports 2 "$@"
