#!/usr/bin/env bash
# Compile the six modules of this directory, one lean process at a time, and check the number
# of axiom reports. Arguments are passed on to check_bridge.py (for example --out DIR).
# ConPACtlSchedulerHalts imports the other five modules.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/ConPACtlSchedulerHalts.lean" --reports 4 --also ConPACtlClosure:5 "$@"
