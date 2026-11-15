#!/usr/bin/env bash
# Compile the modules of this directory with every standalone module they import, one lean
# process at a time. Arguments are passed on to check_bridge.py (for example --out DIR to
# reuse compiled objects). The last module imports the other three.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194GuardedCompile.lean" --reports 7 "$@"
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194TranslateShift.lean" --reports 5 "$@"
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194TranslateSubst.lean" --reports 4 "$@"
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194GuardedEndpoint.lean" --reports 4 "$@"
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194TranslateExt.lean" --reports 7 "$@"
