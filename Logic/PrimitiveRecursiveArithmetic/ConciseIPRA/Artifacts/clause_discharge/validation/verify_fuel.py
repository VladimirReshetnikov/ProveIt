"""Check bounded variants at exact and one-short computation budgets."""
from pathlib import Path
import ast
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def functions(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.Import))]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


def run(path, data, accepted, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    p = subprocess.run(command, input=json.dumps(data), text=True,
                       capture_output=True, timeout=60)
    result = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    if result != accepted:
        raise AssertionError((path.name, accepted, p.returncode, p.stderr[-200:]))


def main():
    results = []
    cli_checks = 0
    profiles = [
        ('deterministic', ROOT / 'validation/examples', False),
        ('explicit', ROOT / 'reference/old_name_examples', True),
    ]
    for profile, directory, object_input in profiles:
        checker = ROOT / 'code' / ('checker_' + profile + '_fuel.py')
        namespace = functions(checker)
        for path in sorted(directory.glob('*.json')):
            data = json.loads(path.read_text())
            goal, proof = (data['goal'], data['proof']) if object_input else data
            namespace['fuel'] = 10**9
            namespace['prove'](goal, proof, [([], [1, 1])])
            used = 10**9 - namespace['fuel']
            if used < 1:
                raise AssertionError('missing budget consumption')
            for optimized in (False, True):
                run(checker, [goal, proof, used], True, optimized)
                run(checker, [goal, proof, used - 1], False, optimized)
                cli_checks += 2
            results.append({'profile': profile, 'file': path.name, 'exact_fuel': used})
        for budget in (-1, True, 1.0, None, [], '1'):
            run(checker, [[0, 0], ['u', 0, 0, None], budget], False)
            cli_checks += 1
    report = {'exact_and_one_short_cases': results,
              'malformed_budget_rejections': 12, 'public_cli_checks': cli_checks,
              'failures': 0}
    (ROOT / 'evidence/fuel_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'cases': len(results), 'cli_checks': cli_checks, 'failures': 0}))


if __name__ == '__main__':
    main()
