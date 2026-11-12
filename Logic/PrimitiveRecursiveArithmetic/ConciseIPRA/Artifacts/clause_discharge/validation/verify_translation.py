"""Replay both translations and exercise the actual standalone CLI."""
from pathlib import Path
import ast
import copy
import json
import subprocess
import sys

import convert
import control_translations as ct
import reference_kernel as ref
import translations as tr

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BASE = ROOT / 'reference'


def functions(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.Import))]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


new = functions(ROOT / 'code/checker_deterministic.py')
control = functions(ROOT / 'code/checker_explicit.py')


def check(cert):
    goal, proof = cert
    new['prove'](goal, proof, [([], [1, 1])])


def reject(cert):
    try:
        check(cert)
    except Exception:
        return
    raise AssertionError('invalid certificate accepted')


def cli(cert, expected=True, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code/checker_deterministic.py')]
    result = subprocess.run(command, input=json.dumps(cert), text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    if accepted != expected:
        raise AssertionError((command, result.returncode, result.stdout, result.stderr[:1000]))


def main():
    examples = HERE / 'examples'
    examples.mkdir(exist_ok=True)
    accepted = {}
    for path in sorted((BASE / 'old_name_examples').glob('*.json')):
        old = json.loads(path.read_text())
        control['prove'](old['goal'], old['proof'], [([], [1, 1])])
        source = convert.certificate_from_selected(old)
        separated = ct.fusion_to_control(source['proof'])
        if ref.derive(separated, [], 0, True) != old['goal']:
            raise AssertionError('initial control conversion failed')
        proof = tr.from_control(separated)
        cert = [old['goal'], proof]
        check(cert)
        reversed_proof = tr.to_control(cert[0], proof)
        if ref.derive(reversed_proof, [], 0, True) != cert[0]:
            raise AssertionError('reverse exact goal failed')
        # Each generated file is also accepted by both ordinary and -O Python.
        cli(cert)
        cli(cert, optimized=True)
        (examples / path.name).write_text(json.dumps(cert, separators=(',', ':')) + '\n')
        accepted[path.stem] = len(json.dumps(cert))
        print('PASS', path.stem, accepted[path.stem], flush=True)
    # Targeted rule-edge examples, independent of the translated fixtures.
    alias = [[1, 0, 3], [1, 0, 0]]
    alias_major = ['i', 0, ['u', 0, 0, None]]
    direct = {
        'active_dispatch_ordinary_elimination':
            [[0, 0], ['e', alias, [0, 0], alias_major, ['u', 0, 0, None]]],
        'active_dispatch_under_successor':
            [[[0, 0], [0, 0]], ['e', alias, [[0, -1], [0, -1]],
             alias_major, ['u', 0, [0, -1], None]]],
        'compound_matrix_ordinary_elimination':
            [[0, 0], ['e', [[0, 0]], [0, 0],
             ['i', [0, 0], ['i', [0, 0], ['u', 0, 0, None]]],
             ['u', 0, 0, None]]],
    }
    for name, cert in direct.items():
        check(cert)
        reverse = tr.to_control(cert[0], cert[1])
        if ref.derive(reverse, [], 0, True) != cert[0]:
            raise AssertionError('direct example reverse translation failed')
        cli(cert)
        cli(cert, optimized=True)
        (examples / (name + '.json')).write_text(json.dumps(cert, separators=(',', ':')) + '\n')
        accepted[name] = len(json.dumps(cert))
        print('PASS', name, accepted[name], flush=True)
    rejected = {}
    def add(name, cert):
        reject(cert)
        cli(cert, False)
        cli(cert, False, True)
        rejected[name] = cert
    add('false_equation', [[0, [0, 0]], ['u', 0, 0, None]])
    add('free_goal', [[-1, -1], ['u', 0, -1, None]])
    add('loose_bound_goal', [[1, 1], ['u', 0, 0, None]])
    add('boolean_goal', [[False, False], ['u', 0, 0, None]])
    add('float_goal', [[0.0, 0.0], ['u', 0, 0, None]])
    add('string_goal', ['[0, 0]', ['u', 0, 0, None]])
    add('negative_index', [[0, 0], ['u', -1, 0, None]])
    add('boolean_index', [[0, 0], ['u', False, 0, None]])
    add('missing_clause', [[0, 0], ['u', 1, 0, None]])
    add('noncanonical_zero', [[[0, 0, 1], [0, 0, 1]], ['u', 0, [0, 0, 1], None]])
    add('invalid_erased_body', [[[0, 0, 999], [0, 0, 999]], ['u', 0, [0, 0, 999], None]])
    add('bad_successor_tag', [[[1, 0], [1, 0]], ['u', 0, [1, 0], None]])
    add('missing_instruction_field', [[0, 0], ['u', 0, 0]])
    add('extra_instruction_field', [[0, 0], ['u', 0, 0, None, 0]])
    add('unknown_instruction', [[0, 0], ['unknown']])
    add('dict_input', {'goal': [0, 0], 'proof': ['u', 0, 0, None]})
    add('missing_input_field', [[0, 0]])
    add('extra_input_field', [[0, 0], ['u', 0, 0, None], 0])
    add('unguarded_base_does_not_name_zero',
        [[0, 0], ['e', [2, 0], [-1, -1],
         ['i', 0, ['u', 0, 0, None]], ['u', 0, -1, None]]])
    add('future_name_escape',
        [[0, 0], ['e', [0, 0], [-2, -2],
         ['i', 0, ['u', 0, 0, None]], ['u', 0, -2, None]]])
    add('major_cannot_use_branch_clause',
        [[0, 0], ['e', [0, 0], [0, 0], ['u', 1, 0, None], ['u', 0, 0, None]]])
    add('zero_row_is_not_a_witness_name',
        [[0, 0], ['e', [0, 0], [-1, -1],
         ['i', 0, ['u', 0, 0, None]], ['u', 0, -1, None]]])
    reject_dir = HERE / 'reject_examples'
    reject_dir.mkdir(exist_ok=True)
    for name, cert in rejected.items():
        (reject_dir / (name + '.json')).write_text(json.dumps(cert, separators=(',', ':')) + '\n')
    result = {'accepted': accepted, 'rejections': list(rejected),
              'exact_goal_reverse_translations': len(accepted),
              'ordinary_and_optimized_cli_checks': 2 * (len(accepted) + len(rejected))}
    (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: len(v) if isinstance(v, (dict, list)) else v for k, v in result.items()}))


if __name__ == '__main__':
    main()
