"""Reproduce the delivered finite checks and complete-source measurements."""
from pathlib import Path
import json
import os
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SCRIPTS = [
    'validation/validate_proofs.py',
    'validation/audit_controls_and_fuel.py',
    'validation/audit_normalization.py',
    'validation/audit_syntax.py',
    'validation/audit_backward_name.py',
    'validation/measure.py',
]


def main():
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for name in SCRIPTS:
        result = subprocess.run([sys.executable, '-B', str(ROOT / name)],
                                cwd=ROOT, env=environment,
                                capture_output=True, text=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        print('PASS', name)
    def read(name):
        return json.loads((ROOT / 'evidence' / name).read_text())
    proofs = read('proof_validation.json')
    controls = read('controls_and_fuel_audit.json')
    normalization = read('normalization_audit.json')
    metric = read('metrics.json')['files']['code/checker.py']
    result = {
        'python': platform.python_version(),
        'all_scripts_passed': True,
        'positive_certificates': proofs['accepted'],
        'negative_certificates': proofs['rejected'],
        'checker_cli_runs': proofs['cli_runs'],
        'source_to_target_translations': proofs['source_to_target_translations'],
        'open_scope_checks': proofs['open_scope_checks'],
        'control_and_fuel_checks': controls,
        'normalization_checks': normalization,
        'selected_checker': metric,
        'backward_name_checks': read('backward_name_audit.json'),
        'backward_name_checker': read('metrics.json')['files']['code/checker_backward_name.py'],
        'limitation': 'Finite implementation evidence, not proof-assistant verification.',
    }
    (ROOT / 'evidence' / 'reproduce.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All packaged checks passed.')
    print('Selected complete checker:', metric['normalized_bytes'], 'bytes,',
          metric['significant_tokens'], 'tokens,', metric['ast_nodes'], 'AST nodes.')


if __name__ == '__main__':
    main()
