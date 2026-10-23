#!/usr/bin/env python3
"""Independent interface/degree audit for the delivered nine-variable source.

Usage: python3 audit_nine_interface.py PATH_TO_DELIVERABLE_ROOT
"""
import gzip
import json
import sys
from itertools import combinations_with_replacement
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main(root):
    data = json.loads((root / 'data/coefficient_recipes.json').read_text())
    pack = json.loads((root / 'data/targets.json').read_text())
    weights = pack['weights'][1:]
    n = len(weights)
    targets = [None] * len(data['rows'])
    for j, target in zip(pack['order'], pack['targets']):
        targets[j] = target
    target_index = {t: j for j, t in enumerate(targets)}
    require(len(target_index) == len(targets), 'Targets not distinct')
    monomials = []
    zero = (0,) * n
    monomials.append((zero, 0))
    for j, w in enumerate(weights):
        ex = list(zero)
        ex[j] = 1
        monomials.append((tuple(ex), w))
    for j, k in combinations_with_replacement(range(n), 2):
        ex = list(zero)
        ex[j] += 1
        ex[k] += 1
        monomials.append((tuple(ex), weights[j] + weights[k]))
    require(len(monomials) == len({v for _, v in monomials}),
            'Degree-two weights not injective')
    reversals = {}
    hits = 0
    for j, row in enumerate(data['rows']):
        for term in row:
            alpha = tuple(term['alpha'])
            e = targets[j] - sum(a * w for a, w in zip(alpha, weights))
            require(e >= 0 and e not in reversals, 'Invalid reversal support')
            reversals[e] = (j, term)
            for beta, weight in monomials:
                if e + weight not in target_index:
                    continue
                require(target_index[e + weight] == j and beta == alpha,
                        'Cross-target contamination')
                hits += 1
    highest = max(reversals)
    j, term = reversals[highest]
    require(highest == max(targets) and not any(term['alpha'])
            and term['leaf'] == 2 and term['sign'] == 1,
            'Missing positive leading coefficient 2')

    ports = [int.from_bytes(gzip.decompress(
        (root / 'coefficients/payloads' / f'{name}.bin.gz').read_bytes()), 'little')
        for name in ['beta', 'K', 'MC', 'MF_source']]
    result = {'target_isolation': 'PASS', 'quadratic_monomials': len(monomials),
              'reversal_terms': len(reversals), 'intended_target_hits': hits,
              'maximum_target': max(targets), 'span': max(targets) + 2 * max(weights),
              'Dcode_leading_coefficient': 2, 'degree_certificates': {}}
    for domain in ['positive', 'natural']:
        base_name = f'multitarget_nine_{domain}'
        cert = json.loads((root / 'nine/generated' / f'{base_name}_degree_certificate.json').read_text())
        raw = json.loads((root / 'nine/generated' / f'{base_name}.json').read_text())
        fixed = {'base_floor': 1 << cert['base_floor_exponent']}
        for recipe in cert['coefficient_recipes']:
            total = 0
            for term in recipe['terms']:
                v = term['coefficient']
                for port, exponent in zip(ports, term['powers']):
                    v *= port ** exponent
                total += v
            fixed[recipe['name']] = total
        degrees_and_coefficients = []
        for node in cert['nodes']:
            kind = node['kind']
            if kind == 'variable':
                value = (1, 1)
            elif kind == 'literal':
                value = (0, node['value'])
            elif kind == 'fixed':
                value = (0, fixed[node['name']])
            else:
                da, a = degrees_and_coefficients[node['left']]
                db, b = degrees_and_coefficients[node['right']]
                if kind == 'mul':
                    value = (da + db, a * b)
                else:
                    degree = max(da, db)
                    a = a if da == degree else 0
                    b = b if db == degree else 0
                    value = (degree, a + b if kind == 'add' else a - b)
            degrees_and_coefficients.append(value)
        degree, lead = degrees_and_coefficients[cert['output']]
        require(degree == cert['degree'] and lead == 1 << 2050,
                'Exact degree/leading coefficient mismatch')
        counts = {k: sum(n['kind'] == k for n in raw['nodes']) for k in ['add', 'sub', 'mul']}
        require(sum(counts.values()) == raw['total_operations'], 'Wrong raw operation count')
        result['degree_certificates'][domain] = {
            'degree': degree, 'exact_diagonal_leading_coefficient': '2^2050',
            'raw_operations': sum(counts.values()), 'raw_operation_counts': counts,
            'degree_certificate_operations': cert['total_operations'],
        }
    result['status'] = 'PASS'
    result['scope'] = 'Independent target support and exact degree arithmetic. Equivalence of raw/certificate formulas is the telescoping identity in the mathematical review.'
    (root/'certificates/nine_interface.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parents[1])
