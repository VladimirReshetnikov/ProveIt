#!/usr/bin/env python3
"""Independent finite checks for the congruence-separated two-root finalizer.

These checks supplement, and do not replace, TEN_ROOT_AUDIT.md.  All arithmetic
uses integers.  The DAG checks bind the actual fixed coefficient byte files.
"""
from pathlib import Path
from functools import reduce
from math import gcd, isqrt
from random import Random
import argparse
import gzip
import hashlib
import json


def square(n):
    return n >= 0 and isqrt(n)**2 == n


def matrix_mul(a, b, modulus):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) % modulus
                 for i in range(2) for j in range(2))


def lucas_mod(parameter, n, modulus):
    """u_0=0,u_1=1,u_(n+2)=parameter*u_(n+1)-u_n."""
    assert n >= 0 and modulus > 0
    out = (1, 0, 0, 1)
    matrix = (parameter % modulus, -1 % modulus, 1, 0)
    while n:
        if n & 1:
            out = matrix_mul(out, matrix, modulus)
        matrix = matrix_mul(matrix, matrix, modulus)
        n >>= 1
    return out[2]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--component', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'ten')
    args = parser.parse_args()
    root = args.component
    raw = (root/'generated/signed10_b2.json').read_bytes()
    dag = json.loads(raw)
    records = json.loads((root/'generated/source_records.json').read_text())
    ports = [int.from_bytes(gzip.decompress((root/'data'/(name+'.bin.gz')).read_bytes()), 'little')
             for name in ('beta', 'K', 'MC', 'MF_source')]
    rng = Random(260923)
    sample_count = 128
    for case in range(sample_count):
        variables = {name: rng.randrange(-17, 18) for name in dag['variables']}
        variables['f'] = case % 29 - 14
        if case % 8 == 0:
            variables['z'] = 0
        if case % 8 == 1:
            variables['x'] = 0
        b = 6*variables['f'] + 4
        modulus = 24*b*b
        fixed = {
            name: sum(row['coefficient'] * reduce(lambda x, y: x*y,
                     (pow(v, e, modulus) for v, e in zip(ports, row['powers'])), 1)
                      for row in rows) % modulus
            for name, rows in records['recipes'].items()
        }
        fixed['beta_source'] = pow(2, 2134940, modulus)
        fixed['beta_mask'] = pow(2, 2134919, modulus)
        values = []
        for node in dag['nodes']:
            kind = node['kind']
            if kind == 'literal':
                value = node['value']
            elif kind == 'fixed':
                value = fixed[node['name']]
            elif kind == 'variable':
                value = variables[node['name']]
            else:
                left, right = values[node['left']], values[node['right']]
                value = left + right if kind == 'add' else left-right if kind == 'sub' else left*right
            values.append(value % modulus)
        n = {name: values[node] for name, node in dag['named_nodes'].items()}
        assert n['b'] == b % modulus
        assert n['base'] % 3 == 1 and n['base'] % (b*b) == 0
        assert n['N0'] % (b*b) == 0 and n['N'] % (b*b) == 0
        assert n['X'] % 3 == 0 and n['X'] % 2 == 1
        assert (n['X']+1) % abs(b) == 0
        assert n['A'] % (4*abs(b)) == 0
        assert n['Pn'] % 3 == 0 and n['Phalf'] % 2 == 0
        assert n['K'] % abs(b) == 0 and n['K'] % 3 == 0
        assert n['Q2'] % (b*b) == 1 and n['Q2'] % 3 == 1
        assert n['Q2'] % 2 == 1
        assert (n['C']+1) % abs(b) == 0
        assert n['D'] % (4*abs(b)) == 0
        assert n['r0'] % (2*abs(b)) == abs(b)
        assert n['r1'] % (2*abs(b)) == 0
        assert n['Ssmall'] % 2 == 1
        c, s, a, d = n['norm_center'], n['Sigma'], n['r0'], n['r1']
        direct = ((c*c-s*s*(a+d))**2-4*s**4*a*d) % modulus
        assert values[dag['output']] == direct
        if variables['z'] == 0 or variables['x'] == 0:
            assert direct == pow(n['Theta'], 4, modulus)

    # Independently test the rational two-root extraction lemma, including
    # negative radicands and nonintegral rational centers.
    root_cases = 0
    rational_searches = 0
    for a in range(-12, 33):
        for d in range(-12, 33):
            if a == d:
                continue
            for denominator in range(1, 6):
                for numerator in range(-30, 31):
                    if gcd(numerator, denominator) != 1:
                        continue
                    rational_searches += 1
                    if (numerator*numerator-(a+d)*denominator**2)**2 != 4*a*d*denominator**4:
                        continue
                    root_cases += 1
                    assert numerator != 0 and denominator == 1
                    assert square(a) and square(d)

    # Signed guard cases include b<0, Q<0, Delta<=0 and positive witnesses.
    guard_cases = guard_zeros = 0
    for t in range(-5, 6):
        b = 6*t+4
        for j in range(-9, 10, 3):
            q = 1+b*b*j
            assert q % 3 == 1 and gcd(b, q) == 1
            r = b*q
            for delta in range(-4, 8):
                for z in range(-7, 8):
                    if z == 0:
                        continue
                    guard_cases += 1
                    a = r+(3*delta-1)*(r*z)**2
                    if square(a):
                        guard_zeros += 1
                        assert square(b) and b >= 4 and square(q) and q > 0
                        assert delta > 0 and a > 0

    # The exact constructive Lucas terms satisfy the residue restrictions.
    # Quotient divisibility is tested by evaluating the numerator modulo its
    # denominator times the desired modulus; gigantic Lucas terms are avoided.
    lucas_cases = 0
    for exponent in range(1, 7):
        b = 4**exponent
        for multiplier in (1, 4, 7):
            X = b*b*multiplier-1
            assert X % 3 == 0 and X % 2 == 1
            for parameter_multiplier in (1, 3, 5):
                A = 4*b*parameter_multiplier
                Pn = 12*b*b*parameter_multiplier
                B = 2*X+1
                h_modulus = (A-2)*b*b
                assert (lucas_mod(A, B, h_modulus)-B) % h_modulus == 0
                k_modulus = (Pn-2)*3*b
                K_residue = lucas_mod(Pn, X+1, k_modulus)
                difference = (K_residue-X-1) % k_modulus
                assert difference % (Pn-2) == 0
                assert difference//(Pn-2) % (3*b) == 2*b
                lucas_cases += 1

    result = {
        'status': 'PASS',
        'scope': 'finite checks supplement the universal proof; not a proof of source undecidability',
        'circuit_sha256': hashlib.sha256(raw).hexdigest(),
        'operation_count': sum(dag['operation_counts'].values()),
        'degree_upper_bound': dag['degree_upper_bound'],
        'actual_coefficient_congruence_samples': sample_count,
        'rational_norm_inputs_examined': rational_searches,
        'rational_norm_zeros_checked': root_cases,
        'signed_guard_inputs_examined': guard_cases,
        'signed_guard_squares_checked': guard_zeros,
        'constructive_lucas_modular_cases': lucas_cases,
    }
    target = Path(__file__).with_name('TEN_ROOT_CHECKS.json')
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
