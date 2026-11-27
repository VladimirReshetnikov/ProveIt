#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p results
python3 code/check_complete_law.py > results/complete_law.json
python3 code/check_radical_transversality.py > results/radical_transversality.json
python3 code/audit_symplectic_counts.py > results/independent_frame_audit.json
python3 code/check_asymptotics.py > results/asymptotics.json
python3 code/minimal_realization.py --self-test > results/minimal_realization.json
python3 code/compression.py code/example_matrix.json > results/example_matrix.json
python3 code/minimal_realization.py code/example_realization.json > results/example_realization.json
python3 - <<'PY'
import json
from pathlib import Path
root = Path('results')
a=json.loads((root/'complete_law.json').read_text())
b=json.loads((root/'radical_transversality.json').read_text())
c=json.loads((root/'independent_frame_audit.json').read_text())
d=json.loads((root/'asymptotics.json').read_text())
e=json.loads((root/'minimal_realization.json').read_text())
assert a['status']=='PASS' and b['passed'] and c['all_passed'] and d['all_passed'] and e['status']=='PASS'
print('All exact checks passed.')
print('Complete law:',a['matrices_checked'],'matrix values and',a['intersection_cells_checked'],'joint cells.')
print('Independent radical count:',b['exact_parameter_comparisons'],'parameter cases.')
print('Independent frame audit:',c['total_matrix_cases'],'matrix cases.')
print('Asymptotic identities:',d['total_matrix_cases'],'matrix cases.')
print('Minimal construction:',e['exhaustive_cross_matrix_instances'],'exhaustive cases and',e['additional_edge_cases'],'edge cases.')
PY
