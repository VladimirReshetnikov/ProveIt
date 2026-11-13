"""Verify the standalone exact-encoder-image entry point.

No finite tests assert the universal second-padding obstruction. They check
the exact predicate and the preservation/rejection behavior of this wrapper.
"""
import ast
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from verify import measure, translate_terminal

ROOT = Path(__file__).resolve().parent
PATH = ROOT / 'code/checker_exact.py'


def exact_formula():
    tree = ast.parse(PATH.read_text())
    module = ast.Module(body=[node for node in tree.body
                             if isinstance(node, ast.FunctionDef)
                             and node.name in ('term', 'formula')], type_ignores=[])
    namespace = {}
    exec(compile(module, '<exact-predicate>', 'exec'), namespace)
    return namespace['formula']


def source_audit():
    exact = ast.parse(PATH.read_text())
    core = ast.parse((ROOT / 'code/checker_bytes587.py').read_text())
    expected = next(node for node in core.body
                    if isinstance(node, ast.FunctionDef) and node.name == 'c')
    actual = next(node for node in exact.body
                  if isinstance(node, ast.FunctionDef) and node.name == 'c')
    if ast.dump(actual) != ast.dump(expected):
        raise ValueError('Exact checker inference core differs from byte587')
    imports = [node for node in ast.walk(exact)
               if isinstance(node, (ast.Import, ast.ImportFrom))]
    if len(imports) != 1 or not isinstance(imports[0], ast.Import) or imports[0].names[0].name != 'json':
        raise ValueError('Unexpected checker dependency')
    return {'inference_core_ast_identical_to_byte587': True,
            'only_import': 'standard-library json'}


def run(job):
    case, optimized = job
    result = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(PATH)],
                            input=json.dumps(case['certificate']), text=True,
                            capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'case': case['name'], 'optimized': optimized, 'expected': case['expected'],
            'accepted': accepted,
            'error': result.stderr.splitlines()[-1] if result.stderr else None}


def main():
    audit = source_audit()
    valid = exact_formula()
    grammar_cases = [
        ('zero reflexivity', [1, 1], True),
        ('first successor padding', [[3], [1]], False),
        ('second successor padding', [[5], [1]], False),
        ('out of range', [[7], [1]], False),
        ('genuine D counter', [[3, 3]], True),
        ('genuine D witness', [[5, 5]], True),
        ('genuine D variable below successor', [[[7], [7]]], True),
        ('genuine iterator accumulator', [[1, 1, 3], 1], True),
        ('iterator counter padding', [[3, 1, 1], 1], False),
        ('iterator seed padding', [[1, 3, 1], 1], False),
        ('guarded D equation', [[[5, 1, 7], [5, 1, 7]]], True),
        ('Boolean masquerading as zero', [True, 1], False),
        ('free negative parameter', [-1, -1], False),
    ]
    grammar_results = []
    for name, goal, expected in grammar_cases:
        result = valid(goal)
        if result != expected:
            raise ValueError('Grammar failure: ' + name)
        grammar_results.append({'name': name, 'goal': goal,
                                'expected': expected, 'actual': result})

    originals = json.loads((ROOT / 'fixtures/terminal_cases.json').read_text())['cases']
    cases = [{'name': row['name'], 'expected': row['expected'],
              'certificate': translate_terminal(row['certificate'])} for row in originals]
    for row in cases:
        if row['expected'] and not valid(row['certificate'][-1]):
            raise ValueError('Positive fixture is noncanonical: ' + row['name'])
    seed = next(row['certificate'] for row in cases if row['expected'])
    for name, goal, expected in grammar_cases:
        if not expected:
            cases.append({'name': 'wrapper_rejects_' + name, 'expected': False,
                          'certificate': seed[:-1] + [goal]})
    cases.append({'name': 'actual_accumulator_zero_computation', 'expected': True,
                  'certificate': [[0, 1, 3, []], [[1, 1, 3], 1]]})
    jobs = [(row, optimized) for row in cases for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [row for row in results if row['accepted'] != row['expected']]
    receipt = {'python': sys.version, 'source_audit': audit,
               'metrics': measure(PATH), 'grammar_checks': grammar_results,
               'cases': len(cases), 'executions': len(results), 'failures': failures,
               'results': results,
               'claim_boundary': 'Exact canonical grammar plus inherited canonical soundness/completeness. No size record. Finite tests do not establish the obstruction theorem.'}
    (ROOT / 'evidence/exact_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in ('results', 'grammar_checks')}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
