"""Verify distributed integrity and repeat the recorded finite checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    manifest_path = ROOT / 'MANIFEST.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        for row in manifest['files']:
            data = (ROOT / row['path']).read_bytes()
            if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
                raise SystemExit('Manifest mismatch: ' + row['path'])
    for relative in ('code/verify.py', 'code/independent_audit.py', 'code/count_nodes.py',
                     'ancillary/verify.py'):
        result = subprocess.run([sys.executable, str(ROOT / relative)],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
    spec = importlib.util.spec_from_file_location('measure', ROOT / 'reference/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    paths = ('code/checker.py', 'reference/generated_checker.py',
             'reference/generated_checker_ast.py')
    measured = {path: measure.metrics(ROOT / path) for path in paths}
    receipt = {
        'python': platform.python_version(),
        'candidate': measured['code/checker.py'],
        'frontier_controls': {p: m for p, m in measured.items() if p.startswith('reference/')},
        'cli': json.loads((ROOT / 'code/validation.json').read_text()),
        'independent': json.loads((ROOT / 'code/independent_audit.json').read_text()),
        'ancillary': json.loads((ROOT / 'ancillary/validation.json').read_text()),
        'ancillary_metrics': json.loads((ROOT / 'ancillary/metrics.json').read_text()),
        'strict_frontier_target_met': False,
    }
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'cli_runs': receipt['cli']['cli_runs'],
                      'independent_checks': receipt['independent']['case_count'],
                      'candidate_metrics': receipt['candidate'],
                      'incidental_coordinate_envelope':
                          receipt['ancillary_metrics']['new_combined_envelope'],
                      'strict_frontier_target_met': False}, indent=2))


if __name__ == '__main__':
    main()
