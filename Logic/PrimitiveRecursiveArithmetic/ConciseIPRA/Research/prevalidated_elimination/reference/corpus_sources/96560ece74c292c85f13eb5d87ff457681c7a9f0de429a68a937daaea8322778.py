"""Reproduce the finite implementation evidence and source comparison."""
from pathlib import Path
import json
import runpy
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    receipts = []
    for name in ['tests/verify.py', 'tests/convert_reference.py',
                 'tests/audit_constructed.py', 'audit_sources.py']:
        result = subprocess.run([sys.executable, str(ROOT / name)], cwd=ROOT,
                                capture_output=True, text=True)
        receipts.append({'script': name, 'exit_code': result.returncode,
                         'stdout': result.stdout, 'stderr': result.stderr})
        if result.returncode:
            print(result.stdout + result.stderr)
            raise SystemExit(result.returncode)
    measure = runpy.run_path(str(ROOT / 'reference/source_measure.py'))['metrics']
    files = ['code/checker.py', 'code/checker_explicit.py', 'code/checker_ast.py',
             'reference/old_checker.py', 'reference/old_checker_ast.py', 'reference/old_folded.py']
    metrics = [{'file': name, **measure(ROOT / name)} for name in files]
    report = {'result': 'PASS', 'scripts': receipts, 'complete_program_metrics': metrics,
              'scope': 'Finite tests and source measurements; not a proof-assistant verification.'}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'result': 'PASS', 'script_count': len(receipts),
                     'selected_metrics': {k: metrics[0][k] for k in
                         ['normalized_tokens', 'ast_nodes', 'normalized_bytes']}}, indent=2))


if __name__ == '__main__':
    main()
