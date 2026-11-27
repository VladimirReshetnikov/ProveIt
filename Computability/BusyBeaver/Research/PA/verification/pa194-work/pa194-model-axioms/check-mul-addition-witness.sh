#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
python3 -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194MulAdditionWitness.lean" --reports 1 "$@"
