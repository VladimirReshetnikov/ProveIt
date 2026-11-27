#!/usr/bin/env python3
"""Run the two exact suites from any working directory (Python standard library)."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)

print('Running exact cyclic checks...', flush=True)
result = subprocess.run([sys.executable, str(ROOT/'code/verify_cyclic_euler.py')],
                        check=True, capture_output=True, text=True)
cyclic = json.loads(result.stdout)
(DATA/'cyclic_euler_verification.json').write_text(result.stdout)
print('Running exact prime-primary checks...', flush=True)
subprocess.run([sys.executable, str(ROOT/'code/verify_pprimary.py'),
                '--output-dir', str(DATA)], check=True)
primary = json.loads((DATA/'pprimary_verification.json').read_text())
assert cyclic['status'] == 'all exact checks passed'
assert cyclic['total_packet_pairs_checked'] == 2453747
assert primary['total_pairs'] == 7964088
summary = {
    'status': 'all exact checks passed',
    'cyclic_packet_pairs': cyclic['total_packet_pairs_checked'],
    'pprimary_packet_pairs': primary['total_pairs'],
    'total_packet_pairs': cyclic['total_packet_pairs_checked'] + primary['total_pairs'],
    'cyclic_cases': cyclic['exhaustive_case_count'],
    'pprimary_cases': len(primary['cases']),
    'cyclic_extremal_constructions': len(cyclic['extremal_construction_checks']),
    'pprimary_subgroup_constructions': len(primary['constructions']),
    'exact_cylinder_fourier_checks': len(cyclic['fourier_norm_checks']),
    'arithmetic': 'integer and exact rational; full value histograms',
    'scope': 'Finite checks corroborate the written general proofs; no Lean or GRH verification is claimed.'
}
(DATA/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
