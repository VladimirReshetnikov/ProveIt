"""Reproduce the delivered proof checks and complete-module measurements."""
from pathlib import Path
import ast
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative):
    result = subprocess.run([sys.executable, str(ROOT / relative)],
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise SystemExit(result.returncode)
    print(relative + ': PASS')


def main():
    run('code/verify.py')
    run('code/independent_kernel_audit.py')
    run('implementation/reproduce.py')
    for name in ['checker', 'control']:
        tree = ast.parse((ROOT / 'code' / (name + '.py')).read_text())
        if (tree.body and isinstance(tree.body[0], ast.Expr)
                and isinstance(tree.body[0].value, ast.Constant)
                and isinstance(tree.body[0].value.value, str)):
            tree.body.pop(0)
        (ROOT / 'code' / (name + '.normalized.py')).write_text(ast.unparse(tree) + '\n')
    report = {
        'deterministic_calculus': json.loads((ROOT / 'code/verification.json').read_text()),
        'independent_kernel_audit': json.loads((ROOT / 'code/independent_kernel_audit.json').read_text()),
        'inherited_implementation': json.loads((ROOT / 'implementation/verification.json').read_text()),
        'inherited_metrics': json.loads((ROOT / 'implementation/metrics.json').read_text()),
        'new_formal_verification': False,
    }
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    print('All delivered checks passed. Evidence: evidence/reproduction.json')


if __name__ == '__main__':
    main()
