#!/usr/bin/env python3
"""Fresh finite affine-envelope audit, independent of the construction script.

Input is a list of all source-outcome contracts with13 duration coordinates:
constant, excess header gap, nine primary counters, first spare value,
remaining spare-list width. This checks the finite coefficient part of the
argument; it does not establish the physical templates or PA calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json

def audit(path, startup):
    data = path.read_bytes()
    contracts = json.loads(data)
    assert len(contracts) == 4778
    by_case = {(c['site'], bool(c['positive'])) for c in contracts}
    assert len(by_case) == len(contracts)
    envelopes = []
    for case in contracts:
        c = case['duration']
        assert len(c) == 13
        assert all(type(x) is int and x >= 0 for x in c)
        assert c[0] >= 1
        register_coefficient = max(c[i] for i in range(2, 11))
        constant = c[0] + 2 * register_coefficient + c[11] + 75 * c[12]
        linear = c[1] + register_coefficient + 3 * c[12]
        envelopes.append((constant, linear, case['site'], bool(case['positive']), c))
    A = max(x[0] for x in envelopes)
    B = max(x[1] for x in envelopes)
    assert (A, B) == (694, 18)
    assert B % 2 == 0
    # Sum_{j=0}^{n-1} (A+B*j) = (B/2)n^2 + (A-B/2)n.
    quadratic, linear = B // 2, A - B // 2
    assert (quadratic, linear) == (9, 685)
    return {
        'contracts_file': path.name,
        'contracts_sha256': hashlib.sha256(data).hexdigest(),
        'contracts': len(contracts),
        'nonnegative_affine_coefficients': True,
        'minimum_constant': min(x['duration'][0] for x in contracts),
        'maximum_step_constant': A,
        'maximum_step_linear': B,
        'constant_maximizer': next({'site': x[2], 'positive': x[3], 'duration': x[4]} for x in envelopes if x[0] == A),
        'linear_maximizer': next({'site': x[2], 'positive': x[3], 'duration': x[4]} for x in envelopes if x[1] == B),
        'cumulative_bound': {'constant': startup, 'linear': linear, 'quadratic': quadratic},
        'source_invariant_premises': {
            'primary_register_sum': 'at most2+j',
            'excess_header_gap': 'at mostj; requires every source address overflow to be0',
            'first_spare_value': 1,
            'remaining_spare_width': 'at most75+3j',
            'absorbing_halt_duration': 1,
        },
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--contracts', type=Path, required=True)
    parser.add_argument('--startup', type=int, default=58066)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.startup >= 0
    receipt = {
        'status': 'PASS',
        'evidence_status': 'Fresh independent finite affine-coefficient audit after recovery',
        'result': audit(args.contracts, args.startup),
        'scope': 'Finite coefficient check conditional on the separately proved uniform physical templates, source bookkeeping, startup, and address closure. No PA-consistency calibration is proved here.',
    }
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
