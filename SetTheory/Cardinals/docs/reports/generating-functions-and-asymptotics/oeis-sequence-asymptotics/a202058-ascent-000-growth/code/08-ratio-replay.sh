#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mode="${1:-core}"
if [[ "$mode" != core && "$mode" != full ]]; then
 echo 'Usage: bash replay.sh [core|full]' >&2; exit 2
fi
python3 scripts/check_manifest.py
out="${A202058_REPLAY_OUT:-$PWD/build/replay}"
mkdir -p "$out"
export A202058_REPLAY_OUT="$out"
python3 scripts/check_core.py | tee "$out/core.json"
python3 scripts/check_tilted_identity.py | tee "$out/tilted-identity.json"
python3 scripts/verify_counterexample.py | tee "$out/counterexample.json"
python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[1])
for name in ['core.json', 'tilted-identity.json', 'counterexample.json']:
    assert json.loads((out/name).read_text()) == json.loads((Path('results')/name).read_text()), name
print('All regenerated core results match the frozen results')
PY
if [[ "$mode" == full ]]; then
 python3 scripts/check_concavity.py 200 180 | tee "$out/factorial.log"
 python3 scripts/check_m_concavity.py 200 180 | tee "$out/rising-factorial.log"
 python3 scripts/compare_replay.py
fi
