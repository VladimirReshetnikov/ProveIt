#!/usr/bin/env python3
"""Independent exact audit of the parent and multi-target quadratic packing.

This code uses only Python's standard library. It does not execute imported
repository code and never decides solvability. Source JSON data are read as
data. A successful run proves the displayed finite polynomial identities.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


def add(a, b, sign=1):
    r = dict(a)
    for m, c in b.items():
        r[m] = r.get(m, 0) + sign * c
        if not r[m]:
            del r[m]
    return r


def mul(a, b):
    r = {}
    for m, c in a.items():
        for n, d in b.items():
            k = tuple(x + y for x, y in zip(m, n))
            r[k] = r.get(k, 0) + c * d
    return {m: c for m, c in r.items() if c}


def shift_positive(poly, variable_count):
    """Apply every witness x_i -> x_i+1; leave four ports unchanged."""
    result = {}
    for monomial, coefficient in poly.items():
        choices = [range(e + 1) for e in monomial[:variable_count]]
        for witness_monomial in itertools.product(*choices):
            c = coefficient
            for before, after in zip(monomial, witness_monomial):
                c *= math.comb(before, after)
            m = tuple(witness_monomial) + monomial[variable_count:]
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(circuit_path, sparse_path, weights_path):
    circuit = json.loads(circuit_path.read_text())
    sparse = json.loads(sparse_path.read_text())
    weights_record = json.loads(weights_path.read_text())
    names = circuit['variables'] + circuit['constants']
    n = len(circuit['variables'])
    size = len(names)
    zero = (0,) * size

    def constant(c):
        return {zero: c} if c else {}

    env = {}
    for i, name in enumerate(names):
        exponents = list(zero)
        exponents[i] = 1
        env[name] = {tuple(exponents): 1}

    def read(x):
        return constant(x) if isinstance(x, int) else env[x]

    for name, op, left, right in circuit['source']:
        assert name not in env
        a, b = read(left), read(right)
        env[name] = mul(a, b) if op == '*' else add(a, b, -1 if op == '-' else 1)
    residuals = [add(read(a), read(b), -1) for a, b in circuit['comparisons']]
    assert len(residuals) == 22 and n == 31
    assert names == sparse['sparse_term_coordinate_order']
    for computed, row in zip(residuals, sparse['equations']):
        stored = {tuple(t['powers']): t['coefficient'] for t in row['terms']}
        assert computed == stored, row['number']
        assert max(sum(m[:n]) for m in computed) == 2

    normalized = [shift_positive(r, n) for r in residuals]
    # Parent row 5 is E-X(a-E); its value at every positive variable 1 is 1.
    fifth_constant = {m: c for m, c in normalized[4].items() if not any(m[:n])}
    assert fifth_constant == {zero: 1}
    order = list(range(4)) + list(range(5, 22)) + [4]
    rows = [normalized[i] for i in order]

    weights = weights_record['weights']
    assert len(weights) == n + 1 and weights[0] == 0
    assert weights == sorted(set(weights))
    pairs = list(itertools.combinations_with_replacement(range(n + 1), 2))
    pair_sums = [weights[i] + weights[j] for i, j in pairs]
    assert len(pairs) == 528 and len(set(pair_sums)) == len(pairs)
    modulus = weights_record.get('modulus')
    if modulus:
        assert len({v % modulus for v in pair_sums}) == len(pairs)
    t = weights[-1]
    targets = [2 * t + j * (2 * t + 1) for j in range(22)]
    total_span = targets[-1] + 2 * t
    assert total_span == 46 * t + 21

    # Form D as (radix exponent, port monomial) -> integer coefficient.
    d = {}
    occupied_row = {}
    for j, row in enumerate(rows):
        for monomial, coefficient in row.items():
            alpha, port = monomial[:n], monomial[n:]
            degree = sum(alpha)
            assert degree <= 2
            weight = sum(e * w for e, w in zip(alpha, weights[1:]))
            radix_exponent = targets[j] - weight
            assert radix_exponent >= 0
            if radix_exponent in occupied_row:
                assert occupied_row[radix_exponent] == j
            occupied_row[radix_exponent] = j
            factor = math.factorial(2 - degree)
            for e in alpha:
                factor *= math.factorial(e)
            key = radix_exponent, port
            d[key] = d.get(key, 0) + factor * coefficient
    d = {m: c for m, c in d.items() if c}
    highest = max(exponent for exponent, _ in d)
    assert highest == targets[-1]
    assert {p: c for (e, p), c in d.items() if e == highest} == {(0,) * 4: 2}

    # Form C(x)^2=(1+sum z_i*x^wi)^2 as literal pair contributions.
    c2 = []
    for left, right in pairs:
        alpha = [0] * n
        if left:
            alpha[left - 1] += 1
        if right:
            alpha[right - 1] += 1
        c2.append((weights[left] + weights[right], tuple(alpha), 1 if left == right else 2))
    extracted = [dict() for _ in targets]
    target_indices = {e: i for i, e in enumerate(targets)}
    for (exponent, port), coefficient in d.items():
        for weight, alpha, factor in c2:
            j = target_indices.get(exponent + weight)
            if j is not None:
                monomial = alpha + port
                p = extracted[j]
                p[monomial] = p.get(monomial, 0) + factor * coefficient
    for actual, row in zip(extracted, rows):
        actual = {m: c for m, c in actual.items() if c}
        assert actual == {m: 2 * c for m, c in row.items()}

    coefficient_l1 = []
    coefficient_port_degree = []
    normalized_counts = []
    for row in rows:
        grouped = {}
        for monomial, coefficient in row.items():
            alpha = monomial[:n]
            grouped[alpha] = grouped.get(alpha, 0) + abs(coefficient)
            coefficient_port_degree.append(sum(monomial[n:]))
        coefficient_l1.extend(grouped.values())
        normalized_counts.append(len(grouped))
    return {
        'status': 'PASS',
        'scope': 'Exact finite symbolic audit; no proof of consistency, solvability, or inherited machine/compiler semantics.',
        'source_sha256': {
            'parent_circuit': digest(circuit_path),
            'parent_sparse_residuals': digest(sparse_path),
            'weight_certificate': digest(weights_path),
        },
        'parent_variables': n,
        'parent_equations': len(rows),
        'parent_maximum_residual_degree': 2,
        'parent_circuit_equals_independent_sparse_residuals': True,
        'all_positive_variables_shifted_by_one': True,
        'row_order_one_based': [i + 1 for i in order],
        'normalized_last_residual_constant': 1,
        'unique_pair_sums': len(pair_sums),
        'maximum_weight': t,
        'targets': targets,
        'total_span': total_span,
        'D_degree': highest,
        'D_leading_coefficient': 2,
        'D_target_extraction_exactly_twice_each_residual': True,
        'formal_D_terms': len(d),
        'normalized_residual_coefficient_counts': normalized_counts,
        'uniform_coefficient_L1_bound': max(coefficient_l1),
        'maximum_coefficient_port_degree': max(coefficient_port_degree),
        'coefficient_bound_rule': 'H=max_l1*(1+abs(beta)+abs(K0)+abs(MC)+abs(MF))^max_port_degree is sufficient.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--circuit', type=Path, required=True)
    parser.add_argument('--sparse', type=Path, required=True)
    parser.add_argument('--weights', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.circuit, args.sparse, args.weights)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

