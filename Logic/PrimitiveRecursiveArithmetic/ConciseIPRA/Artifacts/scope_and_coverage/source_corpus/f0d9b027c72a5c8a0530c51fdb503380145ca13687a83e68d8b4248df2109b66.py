"""Reproduce the source measurements and the finite executable evidence."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
receipts = []
for name in ['measure.py', 'tests/test_checkers.py', 'tests/independent_audit.py', 'tests/mutation_controls.py']:
    run = subprocess.run([sys.executable, str(ROOT / name)], cwd=ROOT,
                         text=True, capture_output=True)
    receipts.append({'script': name, 'exit_code': run.returncode,
                     'stdout': run.stdout, 'stderr': run.stderr})
    if run.returncode:
        print(run.stdout + run.stderr)
        raise SystemExit(run.returncode)
    print(name + ': PASS', flush=True)
result = {'result': 'PASS', 'scripts': receipts,
          'scope': 'Finite executable evidence and static source metrics; not a proof-assistant formalization.'}
(ROOT / 'evidence/reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
checks = json.loads((ROOT / 'evidence/checker_validation.json').read_text())
independent = json.loads((ROOT / 'evidence/independent_result.json').read_text())
lines = [r'\subsection{Finite validation results}',
         f"The delivered suite passes all {checks['runs']:,} public CLI runs: "
         f"{checks['certificate_count']} positive and adversarial certificates across five programs, "
         'ordinary and optimized Python, plus malformed outer-input cases.',
         'The cases include genuine state updates, nested scalar states, contextual equation induction,',
         'nonvacuous witnesses, nested closures, and transport through binders.',
         '',
         f"An independently written evaluator checks {independent['equations_evaluated']:,} generated "
         'zero-instance equations under two old-parameter valuations, with no false evaluated equation.',
         f"A separate named-syntax encoder checks {independent['binding_commutations']} exact binder-substitution "
         'commutations, including both paired variables and nested scalar states.',
         'Three deliberately unsafe mutations admit explicit false equations that the correct checker rejects, both normally and with optimized Python. These are finite diagnostic checks. The universal soundness, completeness, and',
         'bi-interpretability claims rely on the written arguments, not on test counts.']
(ROOT / 'evidence/validation_summary.tex').write_text('\n'.join(lines) + '\n')
print(json.dumps({'result': 'PASS', 'public_cli_runs': checks['runs'],
                  'arithmetic_equations': independent['equations_evaluated'],
                  'binder_commutations': independent['binding_commutations']}, indent=2))
