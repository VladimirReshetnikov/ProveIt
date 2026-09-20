#!/usr/bin/env python3
"""Validate completed saved counts and agreement, without rerunning the search."""
from pathlib import Path
from math import factorial
import json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {0: 0, 3: 0, 6: 0, 9: 0, 12: 0, 15: 84, 18: 3672, 21: 111564}


def check():
    counts = {}
    for filename in ['cpp_through21.json', 'cpp_final_through21.json',
                     'python_through18.json']:
        data = json.loads((ROOT/'data'/filename).read_text())
        assert data['complete'] is True
        expected_lengths = list(range(0, data['max_length']+1, 3))
        assert [row['length'] for row in data['results']] == expected_lengths
        for row in data['results']:
            n = row['length']
            k = n // 3
            assert row['total_words'] == factorial(n)//factorial(k)**3
            assert row['rejected_r2'] == EXPECTED[n]
            assert row['rejected_r3'] == 0
            signature = (row['total_words'], row['rejected_r2'], row['rejected_r3'])
            if n in counts:
                assert counts[n] == signature
            counts[n] = signature
    total = sum(counts[n][0] for n in sorted(counts))
    assert total == 417019279
    for name in ['forward_oracle.json', 'structural_tests.json']:
        assert json.loads((ROOT/'data'/name).read_text())['all_checks_passed']
    return {'all_checks_passed': True, 'balanced_words_accounted_for': total,
            'max_length': max(counts), 'python_cpp_agreement_through_length': 18}

if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
