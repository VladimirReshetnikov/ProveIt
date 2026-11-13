"""Independent targeted falsification of the affine/uniform synthesis.

The arithmetic probe executes the candidate's actual packet branch, captures
its continuation, and evaluates the supplied equation with a separate decoder.
Finite checks do not prove universal soundness or iPRA bi-interpretability.
"""
import ast
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
CANDIDATE = ROOT / 'code' / 'checker.py'


class Budget(Exception):
    pass


def number(tree, environment, valuation, budget):
    budget[0] -= 1
    if budget[0] <= 0:
        raise Budget
    if type(tree) is not list:
        coordinate = int(tree // 1)
        if coordinate < 0:
            return valuation[coordinate]
        return 0 if coordinate == 0 else environment[(coordinate - 1) // 2]
    if len(tree) == 1:
        return 1 + number(tree[0], (0,) + environment, valuation, budget)
    if len(tree) == 3:
        counter, initial, body = tree
        count = number(counter, (0, 0) + environment, valuation, budget)
        result = number(initial, (0, 0) + environment, valuation, budget)
        if count > 18:
            raise Budget
        for _ in range(count):
            result = number(body, (result, result) + environment, valuation, budget)
        return result
    return 0


def arithmetic_probe():
    source = ast.parse(CANDIDATE.read_text())
    source.body = source.body[:-2]  # Remove the public stdin/verdict driver only.
    namespace = {}
    exec(compile(source, str(CANDIDATE), 'exec'), namespace)
    actual_checker = namespace['c']
    captured = []

    def capture(goal, context):
        captured.append((goal, context[-1]))

    namespace['c'] = capture
    scalars = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
               -2.5, -1.5, -0.5, 0.5, 1.5, 2.5, False, True]
    small = scalars + [[], [0], [1], [3], [5], [7], [-1], [-3],
                       [0, 0], [1, 2], [0, 0, 0, 0], [1] * 5]
    rng = random.Random(20261110)

    def tree(depth):
        if depth == 0 or rng.random() < .55:
            return rng.choice(scalars + [None, '', 'x', {}, {'': 0}])
        return [tree(depth - 1) for _ in range(rng.randrange(6))]

    cases = itertools.chain(
        itertools.product(small, scalars, small),
        ((tree(3), tree(3), tree(3)) for _ in range(3000)),
    )
    valuations = [{-3: fresh, -2: old_a, -1: old_b}
                  for fresh, old_a, old_b in itertools.product(range(3), repeat=3)]
    counts = dict(attempts=0, supplied=0, rejected=0, valuations=0, budget_skips=0)
    for predecessor, initial, update in cases:
        counts['attempts'] += 1
        namespace['k'] = -2
        namespace['q'] = lambda: [None, predecessor, initial, update]
        captured.clear()
        try:
            actual_checker([0, 0], [])
        except (TypeError, ValueError, IndexError, RecursionError, KeyError, OverflowError):
            counts['rejected'] += 1
            continue
        if len(captured) != 1:
            raise AssertionError('Expected exactly one arithmetic continuation')
        counts['supplied'] += 1
        _, equation = captured[0]
        for valuation in valuations:
            try:
                left = number(equation[0], (0,), valuation, [10000])
                right = number(equation[1], (0,), valuation, [10000])
            except Budget:
                counts['budget_skips'] += 1
                continue
            if left != right:
                return {'status': 'COUNTEREXAMPLE', 'packet':
                        [None, predecessor, initial, update],
                        'equation': equation, 'valuation': valuation,
                        'left': left, 'right': right, **counts}
            counts['valuations'] += 1
    return {'status': 'PASS_FINITE_UNIFORM_SUPPLY', **counts,
            'scope': 'Actual candidate arithmetic branch; all fresh and old parameter values 0,1,2; independent affine numeric decoder.'}


def public_driver_probe():
    fixture = json.loads((ROOT / 'tests/independent_cases.json').read_text())
    cases = fixture['cases']
    skipped = fixture['skipped_old_format_cases']
    results = []
    for case in cases:
        for optimized in [False, True]:
            run = subprocess.run([sys.executable] + (['-O'] if optimized else [])
                                 + [str(CANDIDATE)], input=json.dumps(case['packet']),
                                 text=True, capture_output=True, timeout=8)
            accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
            results.append({'name': case['name'], 'optimized': optimized,
                            'expected': case['accept'], 'accepted': accepted,
                            'returncode': run.returncode,
                            'stdout': run.stdout,
                            'pass': accepted == case['accept']})
    return {'status': 'PASS' if all(r['pass'] for r in results) else 'FAIL',
            'runs': len(results), 'cases': len(cases),
            'skipped_old_format_cases': skipped, 'results': results}


def main():
    result = {'candidate': str(CANDIDATE.relative_to(ROOT)),
              'sha256': hashlib.sha256(CANDIDATE.read_bytes()).hexdigest(),
              'arithmetic': arithmetic_probe(), 'driver': public_driver_probe(),
              'warning': 'Finite falsification and regression evidence, not universal proof.'}
    destination = ROOT / 'evidence/independent_validation.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({**result, 'driver': {k: v for k, v in result['driver'].items()
                                         if k != 'results'}}, indent=2))
    if result['arithmetic']['status'].startswith('COUNTER') or result['driver']['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
