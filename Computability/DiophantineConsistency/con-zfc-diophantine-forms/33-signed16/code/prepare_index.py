#!/usr/bin/env python3
"""Construct the selected Jones index from the new affine quartic.

This builder shifts the expanded quartic. The independent verifier instead
shifts and squares its twenty-two quadratic residuals.
"""
from collections import defaultdict
from itertools import product
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parents[1]


def main():
    path = ROOT/'quartic31/polynomials.json'
    parent = json.loads(path.read_text())
    nu = len(parent['variables'])
    shifted = defaultdict(int)
    for record in parent['quartic_terms']:
        ex = record['powers']
        positions = [i for i in range(nu) if ex[i]]
        for choices in product(*(range(ex[i]+1) for i in positions)):
            new = list(ex)
            coefficient = record['coefficient']
            for i, r in zip(positions, choices):
                new[i] = r
                coefficient *= math.comb(ex[i], r)
            shifted[tuple(new)] += coefficient
    shifted = {ex: c for ex, c in shifted.items() if c}
    grouped = defaultdict(dict)
    for ex, coefficient in shifted.items():
        alpha = (0,)+ex[:nu]
        factor = math.factorial(4-sum(alpha))*math.prod(math.factorial(j) for j in alpha)
        grouped[alpha][ex[nu:]] = coefficient*factor
    records = []
    for number, (alpha, recipe) in enumerate(sorted(grouped.items())):
        records.append(dict(name=f'c{number:04d}', alpha=list(alpha),
                            expo=sum(x*5**j for j, x in enumerate(alpha)),
                            coefficient_polynomial_in_fixed_ports=[dict(powers=list(ex), coefficient=c)
                                                                  for ex, c in sorted(recipe.items())]))
    binding = json.loads((ROOT/'upstream/compiler/binding.json').read_text())
    sizes = {r['name']: r['bit_length'] for r in binding['files']}
    bits = [sizes[k] for k in ('beta', 'K', 'MC', 'MF_source')]
    bounds = []
    largest = 0
    for row in records:
        sparse = defaultdict(int)
        for term in row['coefficient_polynomial_in_fixed_ports']:
            sparse[sum(x*b for x, b in zip(term['powers'], bits))] += abs(term['coefficient'])
        bound = sum(c << e for e, c in sparse.items())
        exponent = (bound+1).bit_length()
        assert bound+1 < 1 << exponent
        largest = max(largest, exponent)
        bounds.append(dict(name=row['name'], sufficient_index_exponent=exponent,
                           sparse_bound=[dict(exponent=e, multiplier=c) for e, c in sorted(sparse.items())]))
    constants = dict(nu=nu, L=5**(nu+1), fixed_port_order=parent['constants'],
                     coefficient_records=records, index_exponent=largest,
                     z_index=f'2^{largest}', dummy_input=1,
                     y_index='sum((z+c_alpha)*(2*z)^(L-sum(alpha_j*5^j))) for all |alpha|<=4; unlisted c_alpha=0',
                     bounded_sum_cardinality=math.comb(nu+5, 4),
                     parent_path='quartic31/polynomials.json', parent_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                     parent_normalization='The fifth residual at all positive coordinates equal to1 is-1.',
                     compiler_tuple='upstream/compiler/binding.json', actual_port_bit_lengths=bits)
    (ROOT/'data/coefficients31.json').write_text(json.dumps(constants, separators=(',', ':'))+'\n')
    certificate = dict(index_exponent=largest, bounds=bounds, port_bit_lengths=bits,
                       weighted_records=len(records), shifted_terms=len(shifted),
                       claim='Every |c_alpha|+1 is strictly smaller than2^index_exponent.')
    (ROOT/'data/index_bound31.json').write_text(json.dumps(certificate, separators=(',', ':'))+'\n')
    print(json.dumps({k: v for k, v in certificate.items() if k != 'bounds'}, indent=2))


if __name__ == '__main__':
    main()
