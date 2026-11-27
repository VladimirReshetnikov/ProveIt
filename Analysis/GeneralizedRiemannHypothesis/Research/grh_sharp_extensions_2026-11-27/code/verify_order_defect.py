#!/usr/bin/env python3
"""Exact certificates for the trace-and-order theorem's sharpness families.

Uses integer Smith normal forms and then takes p-adic valuations; all
matrices have integral entries and determinants prime to the coefficient
prime, so this computes the Smith profile over Z_p exactly.

The general theorem is proved in order_defect.tex. This program verifies
specific examples, including complete finite-level kernel enumerations.
"""
from __future__ import annotations

import itertools
import argparse
import json
from pathlib import Path

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def unit(d: int, i: int, j: int) -> sp.Matrix:
    z = sp.zeros(d)
    z[i, j] = 1
    return z


def flat(x: sp.Matrix) -> sp.Matrix:
    return sp.Matrix(list(x))  # SymPy's list is row-major.


def relation(rho: list[sp.Matrix], sigma: list[sp.Matrix]) -> sp.Matrix:
    d = rho[0].rows
    basis = [unit(d, i, j) for i in range(d) for j in range(d)]
    blocks = []
    for r, s in zip(rho, sigma):
        blocks.append(sp.Matrix.hstack(*(flat(s * x - x * r) for x in basis)))
    return sp.Matrix.vstack(*blocks)


def vp(x: int, p: int):
    x = abs(int(x))
    if not x:
        return None  # infinity
    n = 0
    while x % p == 0:
        n += 1
        x //= p
    return n


def profile(mat: sp.Matrix, p: int) -> list[int | None]:
    diag = smith_normal_form(mat, domain=sp.ZZ)
    return [vp(diag[i, i], p) for i in range(mat.cols)]


def level_length(exponents, n):
    return sum(n if b is None else min(n, b) for b in exponents)


def enum_kernel(mat: sp.Matrix, p: int, n: int):
    modulus = p ** n
    rows = [[int(x) % modulus for x in row] for row in mat.tolist()]
    count = 0
    for x in itertools.product(range(modulus), repeat=mat.cols):
        if all(sum(a * b for a, b in zip(row, x)) % modulus == 0 for row in rows):
            count += 1
    return count


def exponent_case(p: int, a: int, e: int, enumerate_levels=()):
    I = sp.eye(2)
    E12, E21, E11 = unit(2, 0, 1), unit(2, 1, 0), unit(2, 0, 0)
    rho = [I + p**e * E12, I + E21, I]
    sigma = [I + E12, I + p**e * E21, sp.diag(1, 1 + p**a)]
    mat = relation(rho, sigma)
    actual = profile(mat, p)
    expected = [0, 0, 0, a + e]
    assert actual == expected, (actual, expected)
    rb = sp.Matrix.hstack(*(flat(x) for x in [I, E21, p**e * E12, p**e * E11]))
    sb = sp.Matrix.hstack(*(flat(x) for x in [I, E12, p**e * E21, p**min(a,e) * E11]))
    rp, sy = profile(rb, p), profile(sb, p)
    assert max(rp) == max(sy) == e
    exact = []
    for n in enumerate_levels:
        count = enum_kernel(mat, p, n)
        predicted = p ** level_length(actual, n)
        assert count == predicted
        exact.append({'n': n, 'enumerated_kernel_size': count, 'predicted_size': predicted})
    return {
        'family': 'sharp_exponent_loss', 'p': p, 'a': a, 'e': e,
        'rho_generators': [x.tolist() for x in rho],
        'sigma_generators': [x.tolist() for x in sigma],
        'relation_smith_exponents': actual,
        'rho_order_smith_exponents': rp, 'sigma_order_smith_exponents': sy,
        'trace_witness': int(sp.trace(rho[2]) - sp.trace(sigma[2])),
        'trace_depth_proved_in_text': a,
        'total_length': sum(actual), 'total_bound': a + 3 * e,
        'largest_exponent': max(actual), 'sharp_exponent_bound': a + e,
        'enumeration': exact,
    }


def length_case(p: int, d: int, a: int, e: int, enumerate_levels=()):
    assert p > 1 and d % p and a >= 1 and e >= 1
    I = sp.eye(d)
    common = [I + p**e * unit(d, i, j) for i in range(d) for j in range(d)]
    rho, sigma = common + [I], common + [(1 + p**a) * I]
    mat = relation(rho, sigma)
    actual = profile(mat, p)
    expected = [min(a,e)] * (d*d - 1) + [a]
    assert actual == expected, (actual, expected)
    order_basis = [I] + [p**e * unit(d, i, j)
                         for i in range(d) for j in range(d) if (i,j) != (d-1,d-1)]
    order_profile = profile(sp.Matrix.hstack(*(flat(x) for x in order_basis)), p)
    assert order_profile == [0] + [e] * (d*d-1)
    exact = []
    for n in enumerate_levels:
        count = enum_kernel(mat, p, n)
        predicted = p ** level_length(actual, n)
        assert count == predicted
        exact.append({'n': n, 'enumerated_kernel_size': count, 'predicted_size': predicted})
    return {
        'family': 'sharp_length_coefficient', 'p': p, 'd': d, 'a': a, 'e': e,
        'relation_smith_exponents': actual,
        'image_order_smith_exponents': order_profile,
        'trace_witness': -d * p**a, 'trace_depth_proved_in_text': a,
        'total_length': sum(actual), 'trace_order_bound': a + (d*d-1)*e,
        'sharp_scalar_bound': a+(d*d-1)*min(a,e),
        'finite_levels': [{'n': n, 'length': level_length(actual,n),
                           'trace_order_bound': min(n,a)+(d*d-1)*min(n,e),
                           'sharp_scalar_bound': min(n,a)+(d*d-1)*min(n,a,e)}
                          for n in range(1, max(a,e)+3)],
        'enumeration': exact,
    }


def scalar_case(p: int, a: int, c: int):
    I = sp.eye(2)
    common = [I + p**c * unit(2,0,1), I + p**c * unit(2,1,0)]
    centralizer = profile(relation(common, common), p)
    assert centralizer == [c,c,c,None]
    mat = relation(common+[I], common+[(1+p**a)*I])
    actual = profile(mat, p)
    expected = sorted([a] + [min(a,c)]*3)
    assert actual == expected
    trace_ideal_depth = min(vp(2,p), vp(2+p**(2*c),p))
    return {'family':'scalar_twist_profile','p':p,'scalar_depth':a,'c':c,
            'centralizer_smith_exponents':centralizer,
            'trace_ideal_depth':trace_ideal_depth,
            'trace_depth_proved_in_text':a+trace_ideal_depth,
            'relation_smith_exponents':actual,'total_length':sum(actual),
            'exact_profile_formula':a+3*min(a,c)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data' / 'order_defect_certificates.json')
    args = parser.parse_args()
    cases = []
    for p in (2,3,5):
        for a,e in ((1,1),(1,3),(3,1),(3,2)):
            enums = (1,2,3) if (p,a,e)==(2,1,1) else ()
            cases.append(exponent_case(p,a,e,enums))
    for p,d,a,e in ((3,2,2,1),(3,2,3,2),(3,2,1,3),(2,3,2,1),(5,3,3,2),(3,4,2,1)):
        enums = (1,2) if (p,d,a,e)==(3,2,2,1) else ()
        cases.append(length_case(p,d,a,e,enums))
    for p in (2,3,5):
        for a,c in ((1,2),(2,1),(3,2)):
            cases.append(scalar_case(p,a,c))
    output = {'status':'PASS','arithmetic':'exact integer Smith forms, then p-adic valuations',
              'general_theorem_verified_by':'human-readable proof, not finite computation',
              'case_count':len(cases),'cases':cases}
    target = args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(output, indent=2, default=int)+'\n')
    print(f"PASS: {len(cases)} exact Smith certificates; 5 complete finite-level kernel enumerations.")
    print(f"Wrote {target.name}")


if __name__ == '__main__':
    main()
