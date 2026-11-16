#!/usr/bin/env bash
# Compile the modules of this directory with every standalone module they import, one lean
# process at a time, and check the number of axiom reports. Arguments are passed on to
# check_bridge.py (for example --out DIR to reuse compiled objects).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194EmitterSchedulerPA.lean" --reports 5 \
  --also PA194EmitterScheduler:5 --also PA194EmitterSchedulerCore:3 \
  --also PA194ControllerSchedulerPA:4 \
  --also PA194ControllerScheduler:5 --also PA194ControllerSchedulerCore:3 "$@"
