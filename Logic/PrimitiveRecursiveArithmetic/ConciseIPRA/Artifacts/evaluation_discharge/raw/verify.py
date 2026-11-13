"""Reproduce raw-calculus translations, adversarial checks and CLI tests.

Finite implementation checks supplement the written proof. They are not a
proof of universal soundness or of bi-interpretability.
"""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys

import measure
import translations as tr

ROOT = Path(__file__).resolve().parent


def rejected(module, data):
    try:
        module.check(data)
    except Exception:
        return True
    return False


def negative_cases():
    def r(t):
        return ['u', 0, t, None]
    truth = {'goal': [0, 0], 'proof': r(0)}
    cases = {'false_equation': {'goal': [0, [0, 0]], 'proof': r(0)},
             'not_an_object': [], 'missing_goal': {'proof': r(0)},
             'extra_key': truth | {'extra': 0},
             'not_a_proof': truth | {'proof': {}},
             'empty_proof': truth | {'proof': []},
             'unknown_instruction': truth | {'proof': ['x', 0]},
             'short_use': truth | {'proof': ['u', 0, 0]},
             'long_use': truth | {'proof': ['u', 0, 0, None, None]},
             'boolean_index': truth | {'proof': ['u', False, 0, None]},
             'negative_index': truth | {'proof': ['u', -1, 0, None]},
             'large_index': truth | {'proof': ['u', 1, 0, None]},
             'invalid_major_equation': truth | {'proof': ['e', r(0), r(0), r(0)]},
             'wrong_intro_successor': {'goal': [[1, 0]], 'proof': ['i', [1, 0], 0, ['u', 1, 0, None]]},
             'bad_intro_witness': {'goal': [[0, 0]], 'proof': ['i', [0, 0], -1, ['u', 1, 0, None]]}}
    terms = {'boolean': False, 'float': 0.0, 'free': -1, 'loose_bound': 1,
             'string': '0', 'dict': {}, 'empty': [], 'unary': [0],
             'arity_four': [0, 0, 0, 0], 'successor_tag': [1, 0],
             'loose_iter_body': [0, 0, 2], 'erased_bad_body': [0, 0, True]}
    for name, t in terms.items():
        cases['term_' + name] = {'goal': [t, t], 'proof': r(t)}
    return cases


def main():
    fused = tr.load(ROOT / 'checker.py', 'fused_raw')
    control = tr.load(ROOT / 'control.py', 'control_raw')
    reference = tr.load(ROOT / 'reference/raw_two_case.py', 'pinned_reference')
    counts = {'reference_cases': 0, 'accepted_examples': 0,
              'reference_reverse_replays': 0, 'exact_goal_roundtrips': 0,
              'negative_cases': 0, 'cli_checks': 0}
    for path in sorted((ROOT / 'reference/raw_cases').glob('*.json')):
        data = json.loads(path.read_text())
        result = tr.translate_reference(data, reference, fused)
        tr.translate_reference(data, reference, control, fused=False)
        (ROOT / 'examples' / path.name).write_text(json.dumps(result, indent=2) + '\n')
        counts['reference_cases'] += 1
    for name, data in negative_cases().items():
        (ROOT / 'reject_examples' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    positives = []
    for path in sorted((ROOT / 'examples').glob('*.json')):
        data = json.loads(path.read_text())
        fused.check(data)
        cp = tr.translate(data, fused, control, True, False)
        again = tr.translate(cp, control, fused, False, True)
        if again['goal'] != data['goal']:
            raise ValueError('roundtrip changed goal')
        tr.translate_to_reference(data, fused, reference)
        counts['reference_reverse_replays'] += 1
        counts['exact_goal_roundtrips'] += 1
        counts['accepted_examples'] += 1
        positives.append((path, data))
    negatives = []
    for path in sorted((ROOT / 'reject_examples').glob('*.json')):
        data = json.loads(path.read_text())
        if not rejected(fused, data):
            raise ValueError('adversarial case accepted: ' + path.name)
        counts['negative_cases'] += 1
        negatives.append((path, data))
    for expected, items in [(True, positives), (False, negatives)]:
        for path, data in items:
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'checker.py')]
                run = subprocess.run(command, input=json.dumps(data), text=True,
                                     capture_output=True, timeout=30)
                accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                if accepted != expected:
                    raise ValueError('CLI mismatch: ' + path.name)
                counts['cli_checks'] += 1
    metrics = measure.main()
    result = {'python': sys.version.split()[0], 'status': 'all passed',
              'counts': counts, 'metrics': metrics,
              'limits': 'Finite execution evidence; no universal correctness or new Lean theorem is claimed.'}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
