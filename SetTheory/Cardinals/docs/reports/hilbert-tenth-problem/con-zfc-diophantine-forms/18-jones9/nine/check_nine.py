#!/usr/bin/env python3
"""Finite algebraic checks for nine_compressor.py; no halting claim is tested."""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
from random import Random

import nine_compressor as nc


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def coefficient_add(p, q, factor=1):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, 0) + factor*c
        if not r[a]: del r[a]
    return r


def coefficient_mul(p, q):
    r = {}
    for a, c in p.items():
        for b, d in q.items():
            ex = dict(a)
            for k, v in b: ex[k] = ex.get(k, 0)+v
            key = tuple(sorted(ex.items()))
            r[key] = r.get(key, 0)+c*d
            if not r[key]: del r[key]
    return r


def diagonal_heads(body):
    """Exact leading coefficients over Z[the fixed-leaf symbols].

    A positive-degree cancellation would require more terms and is rejected.
    None occurs in the supplied circuits. Thus the final scalar leader proves
    the stated degree for every specialization of their fixed constants.
    """
    heads = []
    for idx, node in enumerate(body['nodes']):
        k = node['kind']
        if k == 'literal':
            value = node['value']
            out = (0, {(): value}) if value else (-1, {})
        elif k == 'fixed': out = (0, {((node['name'], 1),): 1})
        elif k == 'variable': out = (1, {(): 1})
        else:
            a, b = heads[node['left']], heads[node['right']]
            if k == 'mul':
                out = (-1, {}) if a[0] < 0 or b[0] < 0 else (a[0]+b[0], coefficient_mul(a[1], b[1]))
            else:
                factor = -1 if k == 'sub' else 1
                if a[0] > b[0]: out = a
                elif b[0] > a[0]: out = (b[0], {key: factor*v for key, v in b[1].items()})
                else:
                    coeff = coefficient_add(a[1], b[1], factor)
                    if not coeff:
                        require(a[0] <= 0 or (k == 'sub' and node['left'] == node['right']),
                                f'Unresolved leading cancellation at gate {idx}')
                        out = (-1, {})
                    else: out = (a[0], coeff)
        heads.append(out)
    output = heads[body['output']]
    require(set(output[1]) == {()}, 'Output leader is not coefficient independent')
    named = {}
    for name, idx in body['named_nodes'].items():
        degree, lc = heads[idx]
        named[name] = {'degree': degree,
                       'leading_coefficient': lc.get(()) if set(lc) == {()} else 'symbolic'}
    return output, named


def sparse_ring(n):
    def constant(c): return {(0,)*n: c} if c else {}
    def variable(i): return {tuple(int(j == i) for j in range(n)): 1}
    def power(p, e):
        out = constant(1)
        while e:
            if e & 1: out = nc.mul(out, p)
            p = nc.mul(p, p)
            e //= 2
        return out
    def scale(p, k): return {a: k*c for a, c in p.items() if k*c}
    def minus(p, q): return nc.add(p, scale(q, -1))
    return constant, variable, power, scale, minus


def norm_identity():
    c, x, power, scale, minus = sparse_ring(5)
    T, W, u, v, V = [x(j) for j in range(5)]
    inside = minus(power(T, 2), nc.mul(power(W, 2), nc.add(power(u, 2), nc.mul(power(V, 2), power(v, 2)))))
    norm = minus(power(inside, 2), scale(nc.mul(nc.mul(power(W, 4), power(V, 2)), nc.mul(power(u, 2), power(v, 2))), 4))
    prod = c(1)
    for sa in [-1, 1]:
        for sb in [-1, 1]:
            factor = minus(T, nc.mul(W, nc.add(scale(u, sa), scale(nc.mul(V, v), sb))))
            prod = nc.mul(prod, factor)
    require(prod == norm, 'Four-factor radical norm identity failed')
    return len(norm)


def majorant_identity():
    c, x, power, scale, minus = sparse_ring(2)
    a, b = x(0), x(1)
    bound = nc.add(nc.add(power(a, 2), power(b, 2)), c(1))
    rhs = nc.add(nc.mul(nc.add(power(a, 2), c(1)), power(b, 2)), c(1))
    diff = minus(power(bound, 2), rhs)
    expected = nc.add(nc.add(power(a, 4), power(b, 4)),
                     nc.add(nc.mul(power(a, 2), power(b, 2)), nc.add(scale(power(a, 2), 2), power(b, 2))))
    require(diff == expected, 'Pell square-root majorant identity failed')
    require(all(c >= 0 and all(e % 2 == 0 for e in a) for a, c in diff.items()),
            'Majorant remainder is not a sum of nonnegative even monomials')
    return len(diff)


def h4_identity(nu):
    c, x, power, scale, minus = sparse_ring(1)
    top, L = 5**nu, 5**(nu+1)
    B = x(0)
    hs = [c(1)] + [c(0)]*4
    weights = [power(B, top)] + [power(B, top-5**j) for j in range(nu+1)]
    for w in weights:
        for degree in range(1, 5):
            hs[degree] = nc.add(hs[degree], nc.mul(w, hs[degree-1]))
    h4 = nc.mul(power(B, top), hs[4])
    direct = {(L-nc.expo(a),): 1 for a in nc.all_alphas(nu)}
    require(h4 == direct, f'h4 baseline identity failed for nu={nu}')
    return len(direct)


def tiny_coding_identity():
    """nu=1, P(x,u)=(u-1)^2: exact coefficient of -code^4(z lambda-e)."""
    c, x, power, scale, minus = sparse_ring(1)
    B = x(0)
    L = 25
    # Factorials include the degree slack, which is essential here.
    weighted = {(0, 0): 24, (0, 1): -12, (0, 2): 4}
    z = 2**42
    e = {(L-nc.expo(a),): z+weighted.get(a, 0) for a in nc.all_alphas(1)}
    lam = {(j,): 1 for j in range(4*L)}
    delta = minus(scale(lam, z), e)
    for witness in [0, 1, 2, 3]:
        code = nc.add(c(1), nc.add(B, scale(power(B, 5), witness)))
        encoded = scale(nc.mul(power(code, 4), delta), -1)
        require(encoded.get((L,), 0) == 24*(witness-1)**2,
                'Tiny Jones factorial/coefficient identity failed')
    return 4


def modular_body_checks():
    rng = Random(2151982)
    checks = 0
    for nu in [1, 2]:
        alphas = list(nc.all_alphas(nu))
        coefficients = {a: rng.randrange(-10, 11) for a in alphas}
        coefficients = {a: v for a, v in coefficients.items() if v}
        keys = [(a, f'c{i}') for i, a in enumerate(sorted(coefficients))]
        for weights in ['majorant', 'literal']:
            body = nc.make_body(nu, keys, weights)
            for modulus in [101, 1009]:
                for sample in range(8):
                    z, y = rng.randrange(modulus), rng.randrange(modulus)
                    v = [rng.randrange(modulus) for _ in range(9)]
                    fixed = {'z_index': z, 'y_index': y}
                    fixed.update({name: coefficients[a] for a, name in keys})
                    actual, _ = nc.evaluate_dag(body, fixed, dict(zip(body['variables'], v)), modulus)
                    expected = nc.direct_body_mod(nu, coefficients, z, y, v, modulus, weights)
                    require(actual == expected, f'DAG/direct mismatch at nu={nu}, weights={weights}')
                    checks += 1
    return checks


def combiner_witness_checks():
    count = 0
    for u in range(4):
        for v in range(4):
            a0, a1 = u*u, v*v
            V0, V1 = a0+2, a1+2
            for divisor in [1, 2, 5]:
                for quotient in [0, 1, 3]:
                    dividend = divisor*quotient
                    for margin in [1, 2, 5]:
                        n = (2*margin-1)*(dividend+V0*V1+u+V0*v)-quotient
                        require(n >= 0, 'Constructed combiner witness is negative')
                        W = divisor*(2*margin-1)
                        T = divisor*n+dividend-W*(dividend+V0*V1)
                        value = (T*T-W*W*(a0+V0*V0*a1))**2-4*W**4*V0*V0*a0*a1
                        require(value == 0, 'Constructed norm-combiner witness failed')
                        count += 1
    return count


def run(parent_path, generated):
    parent = json.loads(parent_path.read_text())
    residuals, shifted, total, grouped, weighted = nc.build_parent(parent)
    n = len(parent['variables'])
    # The fifth residual gives a normalization certificate without any port bound.
    values = [1]*n+[2, 3, 4, 5]
    require(nc.polynomial_value(residuals[4], values) == 1, 'Normalization row is incorrect')
    fixed_four = (2, 3, 4, 5)
    actual_pcoef_sum = sum(abs(nc.polynomial_value(p, fixed_four)) for p in weighted.values())
    s_data = json.loads((generated/'index_bound_s.json').read_text())
    s_poly = {tuple(t['powers']): t['coefficient'] for t in s_data['terms']}
    sbound = nc.polynomial_value(s_poly, fixed_four)
    require(actual_pcoef_sum <= sbound-2, 'Explicit coefficient bound fails at diagnostic tuple')
    degree_records = {}
    for weights in ['majorant', 'literal']:
        path = generated/f'nine_{weights}_dag.json'
        body = json.loads(path.read_text())
        output, named = diagonal_heads(body)
        expected_degree = ((161844 if weights == 'majorant' else 291404)*5**(n+1)
                           +(484 if weights == 'majorant' else 860))
        expected_leader = 2**(328 if weights == 'majorant' else 552)
        require(output == (expected_degree, {(): expected_leader}), 'Exact output degree/leader mismatch')
        degree_records[weights] = {'degree': output[0], 'diagonal_leading_coefficient': expected_leader,
                                   'named_ledger': named,
                                   'scope': 'All nine unknowns specialized to t; fixed-leaf symbols retained algebraically. Final leader is a nonzero integer independent of all fixed leaves.',
                                   'sha256': sha256(path.read_bytes()).hexdigest()}
    report = {'status': 'pass',
              'norm_identity_terms': norm_identity(),
              'majorant_nonnegative_remainder_terms': majorant_identity(),
              'h4_exact_terms_by_nu_0_to_3': [h4_identity(nu) for nu in range(4)],
              'tiny_coefficient_identity_checks': tiny_coding_identity(),
              'modular_dag_direct_checks': modular_body_checks(),
              'constructed_combiner_witness_checks': combiner_witness_checks(),
              'degree_certificates': degree_records,
              'scope_limit': 'Finite algebraic checks and exact symbolic degree certificates. The native compiler and Jones/Pell semantic theorems remain mathematical dependencies; this does not decide consistency or provide a new kernel-checked endpoint.'}
    nc.write_json(generated/'nine_checks.json', report)
    return report


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('parent', type=Path)
    ap.add_argument('generated_directory', type=Path)
    args = ap.parse_args()
    out = run(args.parent, args.generated_directory)
    print(json.dumps({k: v for k, v in out.items() if k != 'degree_certificates'}, indent=2))
    print(json.dumps({k: {'degree': v['degree'], 'diagonal_leading_coefficient': v['diagonal_leading_coefficient']}
                      for k, v in out['degree_certificates'].items()}, indent=2))
