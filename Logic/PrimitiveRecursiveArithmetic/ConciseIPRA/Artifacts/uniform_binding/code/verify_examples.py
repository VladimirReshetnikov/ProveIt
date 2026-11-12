"""Portable theorem-level replay, bidirectional recoding, and CLI rejection tests.

The 37 source theorems are inherited counter-evaluation fixtures. This suite
tests the new proof protocol and shared syntax walker; it does not treat the
same theorem's two proof encodings as two independent mathematical results.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys

import translate


ROOT = Path(__file__).resolve().parent.parent


def first_use(proof):
    if type(proof) is not list or not proof:
        return None
    if proof[0] == 'u':
        return proof
    children = {'v': (5, 6), 'e': (2, 3), 'i': (2,)}.get(proof[0], ())
    for index in children:
        found = first_use(proof[index])
        if found is not None:
            return found
    return None


def rejection_cases(positives):
    successor = lambda a: [0, a, 0]
    false = {'goal': [0, successor(0)], 'proof': None}
    cases = {
        'false_equation': false,
        'boolean_term': {'goal': [False, False], 'proof': None},
        'float_term': {'goal': [0.0, 0.0], 'proof': None},
        'string_term': {'goal': ['0', '0'], 'proof': None},
        'object_term': {'goal': [{}, {}], 'proof': None},
        'unbound_positive': {'goal': [1, 1], 'proof': None},
        'unbound_negative': {'goal': [-1, -1], 'proof': None},
        'noncanonical_zero_body': {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': None},
        'malformed_erased_body': {'goal': [[0, 0, False], [0, 0, False]], 'proof': None},
        'empty_goal': {'goal': [], 'proof': None},
        'formula_in_term': {'goal': [[[0, 0], 0, 0], 0], 'proof': None},
        'extra_top_field': {'goal': [0, 0], 'proof': None, 'extra': 1},
        'missing_proof': {'goal': [0, 0]},
        'unknown_instruction': {'goal': [0, successor(0)], 'proof': ['unknown']},
    }
    induction = positives['used_induction_three']
    for label, value in [('boolean', False), ('negative', -1), ('large', 1000000)]:
        altered = copy.deepcopy(induction)
        first_use(altered['proof'])[1] = value
        cases['use_index_' + label] = altered
    for label, value in [('bound_escape', 1), ('free_escape', -999), ('boolean', True)]:
        altered = copy.deepcopy(induction)
        first_use(altered['proof'])[2] = value
        cases['use_witness_' + label] = altered
    altered = copy.deepcopy(induction)
    altered['proof'][2][1] = -1
    cases['introduction_witness_escape'] = altered
    altered = copy.deepcopy(induction)
    altered['proof'].append('extra')
    cases['extra_instruction_field'] = altered
    # These are forced false closed equations: their former right side is
    # replaced by its successor, while the original proof is retained.
    for name, certificate in positives.items():
        if len(certificate['goal']) == 2:
            altered = copy.deepcopy(certificate)
            altered['goal'][1] = successor(altered['goal'][1])
            cases['false_successor_' + name] = altered
    return cases


def run(write=False):
    positives = {}
    round_trips = 0
    for path in sorted((ROOT / 'tests/counter_source').glob('*.json')):
        source = json.loads(path.read_text())
        target = translate.forward(source)
        restored = translate.reverse(target)
        if source['goal'] != target['goal'] or source['goal'] != restored['goal']:
            raise AssertionError(('changed goal', path.name))
        shipped = json.loads((ROOT / 'examples/positive' / path.name).read_text())
        if shipped != target:
            raise AssertionError(('stale target fixture', path.name))
        positives[path.stem] = target
        round_trips += 1
    negatives = rejection_cases(positives)
    checks = []
    for expected, group in [(True, positives), (False, negatives)]:
        for name, certificate in group.items():
            try:
                translate.new.check(certificate)
                observed = True
            except Exception:
                observed = False
            if observed != expected:
                raise AssertionError(('unexpected module outcome', name, expected, observed))
            if write and not expected:
                path = ROOT / 'examples/negative' / (name + '.json')
                path.write_text(json.dumps(certificate, indent=2) + '\n')
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code/checker.py')]
                result = subprocess.run(command, input=json.dumps(certificate), text=True,
                                        capture_output=True, timeout=30)
                observed = result.returncode == 0 and result.stdout == 'ACCEPT\n'
                if observed != expected:
                    raise AssertionError(('unexpected CLI outcome', name, optimized, result.stdout, result.stderr))
                if not expected and (result.returncode == 0 or result.stdout != 'REJECT\n'):
                    raise AssertionError(('incorrect rejection response', name, optimized))
                checks.append({'name': name, 'optimized': optimized, 'accepted': observed})
    result = {
        'positive_theorem_fixtures': len(positives),
        'negative_certificates': len(negatives),
        'literal_goal_bidirectional_round_trips': round_trips,
        'compiler_direction_checks': 2 * round_trips,
        'public_cli_checks': len(checks),
        'mismatches': 0,
        'unused_reflexive_payload_policy': 'A well-formed reflexive goal closes without inspecting its payload, matching the scalar incoming baseline.',
        'checks': checks,
    }
    if write:
        (ROOT / 'evidence/example_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    result = run(write='--write' in sys.argv)
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))
