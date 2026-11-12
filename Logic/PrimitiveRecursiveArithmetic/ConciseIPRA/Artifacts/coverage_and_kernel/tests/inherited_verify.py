"""Offline integration verification for the array-truth u-mode checkers.

The producer and converter are untrusted test support. No checker imports
this file. --write refreshes saved fixtures and the validation receipt;
ordinary verification leaves delivered files unchanged.
"""
import argparse
import copy
import json
import pathlib
import subprocess
import sys
import tempfile

import build_cases
from protocol import translate

ROOT = pathlib.Path(__file__).resolve().parent.parent


def case(name, packet, expected, meaning):
    return {'name': name, 'packet': packet, 'accept': expected, 'meaning': meaning}


def cases():
    inherited = build_cases.build_cases()
    result = [case(row['name'], translate(row['packet']), row['accept'], row['meaning'])
              for row in inherited]
    result.extend([
        case('initial_array_truth', [[]], True, 'The initial [] hypothesis denotes the derived truth 0=0.'),
        case('scalar_zero_is_not_array_truth', [0], False, 'The initial context contains no scalar zero.'),
        case('boolean_false_is_not_array_truth', [False], False, 'False compares equal to numeric zero, not the list truth.'),
        case('fractional_scalar_major', [[0.5, [0], 0, [0, 0]], [0, [0]]], False, 'A numeric major cannot be proved in the live list context.'),
        case('negative_scalar_major', [[-1, [0], 0, [0, 0]], [0, [0]]], False, 'A negative scalar major has no scalar hypothesis.'),
        case('null_major_is_not_array_truth', [[None, [0], 0, [0, 0]], [0, [0]]], False, 'Null is not the absent-major marker of this protocol.'),
        case('bare_false_equation', [[0, [0]]], False, 'The closed false equation 0=1 has no proof packet.')
    ])
    forbidden = next(row for row in result if row['name'] == 'forbidden_compound_progress')
    source_attack = copy.deepcopy(forbidden['packet'])
    for command in source_attack[:-1]:
        if command[0] == [] and not command[2]:
            command[1] = command[2]
    source_attack[-2][1] = 1
    result.append(case('compound_source_attack', source_attack, False,
                       's=1 must not select compound progress; only the false-valued u is the mode.'))
    target_attack = copy.deepcopy(source_attack)
    target_attack[-2][2] = 1
    result.append(case('compound_truthy_u_attack', target_attack, False,
                       'A truthy u selects arithmetic rather than compound induction.'))
    valid = next(row for row in result if row['name'] == 'compound_case_nested_closure')
    source_irrelevant = copy.deepcopy(valid['packet'])
    for command in source_irrelevant[:-1]:
        if command[0] == [] and not command[2]:
            command[1] = 1
    result.append(case('introduction_source_is_unused', source_irrelevant, True,
                       'Changing unused s fields does not change a correctly chosen case or progress mode.'))
    return result


def accepted(program, packet, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(program)]
    process = subprocess.run(command, input=json.dumps(packet), text=True,
                             capture_output=True, timeout=15)
    return process.returncode == 0 and process.stdout == 'ACCEPT\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    examples = cases()
    programs = ('checker.py', 'checker_bytes.py', 'checker_joint.py', 'readable_checker.py')
    rows = []
    for example in examples:
        for name in programs:
            for optimized in (False, True):
                got = accepted(ROOT / 'code' / name, example['packet'], optimized)
                rows.append({'case': example['name'], 'program': name,
                             'optimized': optimized, 'expected': example['accept'],
                             'accepted': got, 'matches': got == example['accept']})

    # This mutation resurrects the specific compound-induction bug caught
    # during review. Its successful run is evidence that the negative
    # certificate exercises the mode guard, not merely unrelated bad syntax.
    attack = next(row['packet'] for row in examples if row['name'] == 'compound_source_attack')
    source = (ROOT / 'code' / 'checker_bytes.py').read_text()
    old = 'len(a) % 2 == u'
    if source.count(old) != 1:
        raise ValueError('Unexpected checker source for the scoped mutation')
    mutation_rows = []
    with tempfile.TemporaryDirectory() as directory:
        mutation = pathlib.Path(directory) / 'unsafe_source_mode.py'
        mutation.write_text(source.replace(old, 'len(a) % 2 == s'))
        for optimized in (False, True):
            got = accepted(mutation, attack, optimized)
            mutation_rows.append({'mutation': 'source_field_selects_progress',
                                  'optimized': optimized, 'expected': True,
                                  'accepted': got, 'matches': got})
    failed = [row for row in rows + mutation_rows if not row['matches']]
    summary = {'examples': len(examples), 'programs': len(programs),
               'ordinary_and_optimized_cli_runs': len(rows),
               'mutation_cli_runs': len(mutation_rows), 'mismatches': len(failed)}
    receipt = {'summary': summary, 'results': rows, 'mutation_results': mutation_rows,
               'scope': 'Finite integration and negative-control evidence; not a proof-assistant formalization.'}
    if args.write:
        fixtures = ROOT / 'tests' / 'fixtures'
        fixtures.mkdir(exist_ok=True)
        for example in examples:
            (fixtures / (example['name'] + '.json')).write_text(json.dumps(example['packet']) + '\n')
        (ROOT / 'tests' / 'cases.json').write_text(json.dumps(
            [{k: v for k, v in row.items() if k != 'packet'} for row in examples], indent=2) + '\n')
        (ROOT / 'evidence' / 'array_truth_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if failed:
        print(json.dumps(failed, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
