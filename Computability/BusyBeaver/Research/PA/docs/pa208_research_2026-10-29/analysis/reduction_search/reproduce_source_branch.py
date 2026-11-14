#!/usr/bin/env python3
"""Regenerate the scoped source experiments and verify the zero certificate."""
from pathlib import Path
import json,subprocess,sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
commands=[
 ['analysis/reduction_search/remove_mp_padding.py'],
 ['analysis/reduction_search/remove_dead_transfer.py'],
 ['analysis/reduction_search/mp_success_variants.py'],
 ['analysis/reduction_search/direct_selection.py'],
 ['analysis/reduction_search/no_mp_padding/prove_source_zero.py'],
 ['analysis/reduction_search/no_mp_padding/prove_source_zero.py','--certificate',
  'analysis/reduction_search/no_mp_padding/source_zero_certificate.json'],
]
for command in commands:
    result=subprocess.run([sys.executable,*command],cwd=ROOT,capture_output=True,text=True)
    if result.returncode:
        sys.stdout.write(result.stdout);sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    print('PASS',command[0], '(saved certificate verification)' if '--certificate' in command else '')
summary={
 'source_alternatives':4+len(json.loads((HERE/'direct_selection/report.json').read_text())),
 'checked_zero_edges':json.loads((HERE/'no_mp_padding/source_zero_certificate.json').read_text())['checked_edges'],
 'literal_state_claim':'No sub-208 machine follows from these source experiments',
 'new_selection_cases_are_finite_checks':True,
 'all_natural_arguments':['no_mp_padding/proof.md','direct_selection/proof.md'],
}
print(json.dumps(summary,indent=2))
