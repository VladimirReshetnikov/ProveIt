#!/usr/bin/env python3
"""Independent exact checks and reproducible data. No third-party dependencies.

Run: python code/verify.py --out data
The finite checks complement, but do not replace, the all-parameter article proofs.
"""
from __future__ import annotations
import argparse
import csv
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from catalan_hankel import (
    coefficients, hankel_direct, hankel_formula, shifted_catalan_hankel,
    generating_function, denominator_coefficients, minimal_denominator,
    small_determinant_formula, barry_printed_coefficient, minor, leading_constant,
    poly_eval, poly_mul, bareiss, R,
)


def differences(values):
    return [values[i+1]-values[i] for i in range(len(values)-1)]


def poly_trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_remainder(p, q):
    p = poly_trim([Fraction(x) for x in p])
    q = poly_trim([Fraction(x) for x in q])
    while len(p) >= len(q) and any(p):
        k = len(p)-len(q)
        scale = p[-1]/q[-1]
        for j, c in enumerate(q):
            p[k+j] -= scale*c
        p = poly_trim(p)
    return p


def relatively_prime(p, q):
    while any(q):
        p, q = q, poly_remainder(p, q)
    return len(poly_trim(p)) == 1


def newton_power_coefficients(values):
    """Interpolate at 0,1,... into ascending rational power coefficients."""
    out = [Fraction(0)]*len(values)
    basis = [Fraction(1)]
    work = list(values)
    for k in range(len(values)):
        for j, value in enumerate(basis):
            out[j] += work[0]*value
        work = differences(work)
        basis = [x/Fraction(k+1) for x in poly_mul(basis, [-k, 1])]
    return poly_trim(out)


def run(out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    counts = {}
    comparisons = 0
    # N+1 distinct a-values certify a polynomial row for each fixed (N,m).
    for m in range(13):
        for N in range(13):
            for a in range(N+1):
                assert hankel_direct(N, m, a, 1) == hankel_formula(N, m, a, 1)
                comparisons += 1
    counts['direct_polynomial_evaluation_checks'] = comparisons
    counts['coefficient_polynomials_certified_for_fixed_N_m'] = 13*13

    parameter_pairs = [(1, 1), (2, 3), (0, 5), (-4, 1), (-8, 2),
                       (-1, 1), (3, 0), (0, 0), (-3, -2), (2, -3)]
    count = 0
    for m in range(9):
        for N in range(9):
            for a, b in parameter_pairs:
                assert hankel_direct(N, m, a, b) == hankel_formula(N, m, a, b)
                count += 1
    counts['additional_direct_signed_and_degenerate_checks'] = count

    count = 0
    for s in range(2, 13):
        for N in range(1, 13):
            for k in range(N+1):
                assert barry_printed_coefficient(N-1, k, s) == coefficients(N, s-1)[k]
                count += 1
    counts['printed_coefficient_shift_checks'] = count
    assert sum(barry_printed_coefficient(0, k, 2) for k in range(2)) == 3
    assert hankel_direct(1, 2, 1, 1) == 7

    count = 0
    for m in range(7):
        for N in range(13):
            for a, b in [(1, 1), (2, 3), (-4, 1), (-1, 1)]:
                assert small_determinant_formula(N, m, a, b) == hankel_formula(N, m, a, b)
                count += 1
    counts['confluent_small_determinant_checks'] = count

    minor_data = []
    count = 0
    for m in range(8):
        d = m*(m-1)//2
        for ell in range(m+1):
            values = [minor(N, m, ell) for N in range(2*d+2)]
            powers = newton_power_coefficients(values)
            assert len(powers) == d+1
            expected = leading_constant(m)*comb(m, ell)
            assert powers[-1] == expected
            if d >= 1:
                correction = Fraction(d*(m+2)-(m-1)*ell, 2)
                assert powers[-2] == expected*correction
            for N in [-9, -3, -1, 2*d+5]:
                assert poly_eval(powers, N) == minor(N, m, ell)
            minor_data.append({'m':m, 'ell':ell,
                               'coefficients': [str(x) for x in powers]})
            count += 1
    counts['minor_polynomials_exactly_interpolated_and_checked'] = count

    gf_data = []
    rec_checks = 0
    symmetry_checks = 0
    for m in range(11):
        d, K = m*(m-1)//2, (m-1)**2
        sign = (-1)**((m-1)*(m-2)//2)
        for a, b in [(1,1), (2,3), (-1,1), (1,2)]:
            p, q = generating_function(m, a, b)
            values = [hankel_formula(N, m, a, b) for N in range(2*len(q)+25)]
            for N in range(K+1, len(values)):
                assert sum(q[j]*values[N-j] for j in range(min(N,len(q)-1)+1)) == 0
                rec_checks += 1
            assert p[0] == 1
            assert p[-1] == sign*b**K
            assert relatively_prime(p, [1,-a-2*b,b*b])
            for j in range(K//2+1):
                assert p[K-j] == sign*b**(K-2*j)*p[j]
                symmetry_checks += 1
            if m <= 7:
                gf_data.append({'m':m, 'a':a, 'b':b, 'numerator':p, 'denominator':q})
    counts['recurrence_coefficient_checks'] = rec_checks
    counts['numerator_reciprocity_checks'] = symmetry_checks
    counts['generic_minimality_polynomial_gcd_checks'] = 11*4

    degenerate = 0
    for m in range(11):
        for a,b in [(0,1),(-4,1),(3,0),(0,0)]:
            q = minimal_denominator(m,a,b)
            L = len(q)-1
            values = [hankel_formula(N,m,a,b) for N in range(2*L+15)]
            p = [sum(q[j]*values[N-j] for j in range(min(N,L)+1)) for N in range(L+1)]
            p = poly_trim(p)
            assert relatively_prime(p,q)
            for N in range(max(L,1),len(values)):
                assert sum(q[j]*values[N-j] for j in range(min(N,L)+1)) == 0
            degenerate += 1
    counts['exceptional_minimal_denominator_checks'] = degenerate

    # Exact two-exponential expansion with rational characteristic roots.
    # a=1,b=2 gives r_+=2,r_-=1/2 and lambda_+=4,lambda_-=1.
    count = 0
    branch_data = []
    for m in range(8):
        d = m*(m-1)//2
        Qs = []
        for r in [Fraction(2),Fraction(1,2)]:
            vals = [sum((-1)**(m+ell)*minor(N,m,ell)*r**ell
                        for ell in range(m+1)) for N in range(d+1)]
            Qs.append(newton_power_coefficients(vals))
        y, delta = Fraction(1,2), Fraction(3,2)
        plus = [(Fraction(2)-1)*v/(y**m*delta) for v in Qs[0]]
        minus = [-(Fraction(1,2)-1)*v/(y**m*delta) for v in Qs[1]]
        assert plus[-1] == leading_constant(m)*Fraction(2)**(m+1)/3
        if d:
            assert plus[-2]/plus[-1] == d*(Fraction(m,2)-1)
        for N in range(21):
            assert poly_eval(plus,N)*4**N + poly_eval(minus,N) == hankel_formula(N,m,1,2)
            count += 1
        branch_data.append({'m':m,'a':1,'b':2,'lambda_plus':4,'lambda_minus':1,
                            'P_plus':[str(x) for x in plus],
                            'P_minus':[str(x) for x in minus]})
    counts['exact_two_branch_checks'] = count

    # Coefficient positivity and normalized strict log-concavity.
    count = 0
    for m in range(13):
        for N in range(2,31):
            c = coefficients(N,m)
            assert all(x > 0 for x in c)
            for k in range(1,N):
                assert Fraction(c[k],comb(N,k))**2 > (
                    Fraction(c[k-1],comb(N,k-1))*Fraction(c[k+1],comb(N,k+1)))
                count += 1
    counts['strict_ultra_log_concavity_checks'] = count

    with (out_dir/'sequences.csv').open('w',newline='') as fh:
        writer=csv.writer(fh)
        writer.writerow(['m','a','b','N','D_N'])
        for m in range(9):
            for a,b in [(1,1),(2,3),(1,2),(0,1),(-4,1)]:
                for N in range(31):
                    writer.writerow([m,a,b,N,hankel_formula(N,m,a,b)])
    (out_dir/'coefficient_rows.json').write_text(json.dumps([
        {'N':N,'m':m,'coefficients':coefficients(N,m)}
        for m in range(9) for N in range(13)],indent=2)+'\n')
    (out_dir/'generating_functions.json').write_text(json.dumps(gf_data,indent=2)+'\n')
    (out_dir/'minor_polynomials.json').write_text(json.dumps(minor_data,indent=2)+'\n')
    (out_dir/'two_branch_polynomials.json').write_text(json.dumps(branch_data,indent=2)+'\n')
    report={'status':'PASS','arithmetic':'exact integers and fractions only',
            'dependencies':'Python standard library only', 'checks':counts,
            'note':'Finite verification is independent evidence; all-parameter proofs are in the article.'}
    (out_dir/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    run(parser.parse_args().out)
