"""Finite truth-sequence checks accompanying the written closure theorem.

This checks Boolean instances; it is not a proof of the arithmetic theorem.
"""
import itertools
import json
from pathlib import Path


def check():
    cases = 0
    for length in range(1, 13):
        for values in itertools.product((False, True), repeat=length):
            base = values[0]
            conditional = not base or all(values)
            progressive = all(not a or b for a, b in zip(values, values[1:]))
            anchored_progress = not base or progressive
            false_base_progress = base or progressive
            assert not progressive or conditional
            assert conditional == anchored_progress
            assert (conditional == progressive) == false_base_progress
            cases += 1
    result = {
        'finite_sequences_checked': cases,
        'maximum_sequence_length': 12,
        'failures': 0,
        'counterexample': {'E': [False, True, False], 'conditional': True, 'progressive': False},
        'scope': 'Finite Boolean checks only; the report supplies the intuitionistic proof.'
    }
    root = Path(__file__).resolve().parent
    (root / 'evidence/closure_criterion_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    check()
