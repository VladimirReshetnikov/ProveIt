#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git rev-parse --show-toplevel)
python3 -X utf8 -B "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194ExPositiveMembershipAudit.lean" --reports 16 "$@"
