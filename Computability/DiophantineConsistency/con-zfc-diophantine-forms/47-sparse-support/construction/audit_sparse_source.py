#!/usr/bin/env python3
"""Independent finite certificate for support-sensitive quadratic extraction.

Reads mathematical JSON data only; no upstream code is imported or executed.
This is a finite algebra check, not a proof of the inherited compiler theorem.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('targets', type=Path)
    ap.add_argument('weights', type=Path)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    targets_bytes = args.targets.read_bytes()
    d = json.loads(targets_bytes)
    wd = json.loads(args.weights.read_bytes())
    w = wd['weights']
    if len(w) == 31:
        w = [0] + w
    require(len(w) == 32 and w[0] == 0, '32 positions with constant at zero required')
    require(min(w[1:]) > 0 and len(set(w)) == 32, 'distinct positive variable positions required')
    W = max(w)
    pair_sums = defaultdict(list)
    for i in range(32):
        for j in range(i, 32):
            pair_sums[w[i] + w[j]].append((i, j))
    support = {tuple(term['alpha']) for row in d['rows'] for term in row['terms']}
    isolated = []
    for alpha in sorted(support):
        pair = [i+1 for i, e in enumerate(alpha) for _ in range(e)]
        require(len(pair) <= 2, 'nonquadratic source term')
        pair = tuple(sorted([0] * (2-len(pair)) + pair))
        value = w[pair[0]] + w[pair[1]]
        require(pair_sums[value] == [pair], f'selected pair not isolated: {pair}')
        isolated.append({'pair': list(pair), 'sum': value})
    spacing = 2*W + 1
    offset = d.get('target_offset', 0)
    target_list = [j*spacing + offset for j in range(1, 23)]
    collision_checks = 0
    for source_row, row in enumerate(d['rows']):
        for term in row['terms']:
            alpha = term['alpha']
            source_exponent = sum(a*x for a, x in zip(alpha, w[1:]))
            code_exponent = target_list[source_row] - source_exponent
            require(code_exponent >= 0, 'negative exponent')
            for total, pairs in pair_sums.items():
                exponent = code_exponent + total
                collision_checks += len(pairs)
                if exponent in target_list:
                    require(exponent == target_list[source_row], 'cross-row contribution')
                    require(total == source_exponent and len(pairs) == 1, 'wrong selected monomial')
    p = max(target_list) + 3*W + 2
    t = 2*p
    degree = 1152*t + 8*W + 280
    result = {
        'status': 'PASS',
        'source_sha256': hashlib.sha256(targets_bytes).hexdigest(),
        'weights': w,
        'maximum_weight': W,
        'selected_monomials': len(support),
        'all_padded_pairs': 528,
        'distinct_pair_sums': len(pair_sums),
        'irrelevant_pair_collisions': 528-len(pair_sums),
        'weighted_source_records': sum(len(row['terms']) for row in d['rows']),
        'all_record_pair_cross_target_checks': collision_checks,
        'target_spacing': spacing,
        'target_offset': offset,
        'targets': target_list,
        'N_base_exponent': p,
        'N_degree': t,
        'F9_exact_degree_from_proved_ledger': degree,
        'F9_diagonal_leading_coefficient': {
            'power_of_two': 2050,
            'power_of_scaled_base_coefficient': 1152*p + 4*W,
        },
        'isolated_pairs': isolated,
        'limitations': 'Degree follows from the accompanying symbolic proof; this finite audit is not a ZFC or Lean semantic certificate.'
    }
    output = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(output)
    print(json.dumps({k: v for k, v in result.items() if k not in ('isolated_pairs', 'weights', 'targets')}, indent=2))


if __name__ == '__main__':
    main()
