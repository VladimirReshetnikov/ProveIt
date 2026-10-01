#!/usr/bin/env python3
"""Exact certificates for uniform smoothing and commensurate-mask stabilization.

Python standard library only. The finite certificates are exact; the general
eventual-positivity theorem is proved analytically using classical Polya positivity.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb, factorial
from pathlib import Path
import json

# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result beside itself, with CRLF on Windows). Pass
# --output-dir with this program's own directory, on a copy, to regenerate
# the recorded file.
def _ed_write(name, text):
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def mul(a, b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def trim(a):
    a = list(a)
    while len(a)>1 and a[-1] == 0:
        a.pop()
    return a


def divide(a, b):
    a = trim(a)
    q = [F(0)]*max(1, len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        k = len(a)-len(b)
        v = a[-1]/b[-1]
        q[k] = v
        for j, x in enumerate(b):
            a[k+j] -= v*x
        a = trim(a)
    return trim(q), a


def bracket_product(caps):
    p = [F(1)]
    for cap in caps:
        p = mul(p, [F(1)]*cap)
    return p


def falling(n, k):
    p = 1
    for j in range(k):
        p *= n-j
    return p


def polya_coefficients(p, n):
    return [sum(p[j]*comb(n,k-2*j) for j in range(len(p)) if 0<=k-2*j<=n)
            for k in range(n+2*(len(p)-1)+1)]


def bernstein_row(r, p, cell):
    d = mul([F((-1)**k*comb(r,k)) for k in range(r+1)], p)
    degree = r-1
    direct = [sum(d[k]*(cell-k)**(degree-ell)*(cell+1-k)**ell
                  for k in range(min(cell+1,len(d)))) for ell in range(r)]
    power = [sum(d[k]*comb(degree,v)*(cell-k)**(degree-v)
                 for k in range(min(cell+1,len(d)))) for v in range(r)]
    converted = [sum(power[v]*F(comb(ell,v),comb(degree,v)) for v in range(ell+1))
                 for ell in range(r)]
    assert direct == converted
    return direct


def check_sharp_example():
    p = [F(1),F(-1),F(1)]
    value8 = bernstein_row(8,p,5)[0]/factorial(7)
    assert value8 == F(-17,2520)
    rows = [bernstein_row(9,p,j) for j in range(11)]
    assert all(x>=0 for row in rows for x in row)
    assert all(rows[j] == list(reversed(rows[10-j])) for j in range(11))
    integral = sum(sum(row) for row in rows)/F(9*factorial(8))
    assert integral == 1
    witnesses = []
    for n in range(12):
        coeff = polya_coefficients(p,n)
        if min(coeff)<0:
            k = next(k for k,x in enumerate(coeff) if x<0)
            witnesses.append(dict(order=n,index=k,value=str(coeff[k])))
        else:
            assert n == 11
    return dict(order8_center=str(value8),order9_bernstein_rows=[[int(x) for x in row] for row in rows],
                integral=str(integral),least_smoothing_order=9,first_half_step_certificate=11,
                half_step_coefficients=[int(x) for x in coeff],earlier_half_step_obstructions=witnesses)


def check_falling_identity():
    polynomials = [[F(1),F(-1),F(1)],[F(1),F(-3,2),F(1)],
                   [F(1),F(-2),F(2)],[F(1),F(-1),F(1),F(-1),F(1)]]
    count = 0
    certificates = []
    for p in polynomials:
        d = 2*(len(p)-1)
        for n in range(21):
            values = polya_coefficients(p,n)
            total = n+d
            for k, value in enumerate(values):
                rhs = sum(p[j]*F(falling(k,2*j)*falling(total-k,d-2*j),falling(total,d))
                          for j in range(len(p)))
                assert value/F(comb(total,k)) == rhs
                count += 1
        n = 0
        while True:
            values = polya_coefficients(p,n)
            if min(values)>=0:
                certificates.append(dict(polynomial=[str(x) for x in p],order=n,
                                         coefficients=[str(x) for x in values]))
                break
            n += 1
    return dict(coefficient_identities=count,positive_axis_examples=certificates)


def check_divisor_criterion():
    lists = [c for k in range(4) for c in combinations_with_replacement(range(1,7),k)]
    polys = {c: bracket_product(c) for c in lists}
    counts = dict(pairs=0,divisible=0,divisible_with_negative_coefficient=0)
    for a in lists:
        for b in lists:
            q, rem = divide(polys[a],polys[b])
            divisor = all(sum(x%d==0 for x in a)>=sum(x%d==0 for x in b) for d in range(2,7))
            assert (rem == [0]) == divisor, (a,b)
            counts['pairs'] += 1
            if divisor:
                assert q[0] == q[-1] == 1
                assert all(x.denominator == 1 for x in q)
                counts['divisible'] += 1
                counts['divisible_with_negative_coefficient'] += min(q)<0
    return counts


def main():
    result = dict(status='passed',arithmetic='exact rational and integer',
                  sharp_example=check_sharp_example(),polya=check_falling_identity(),
                  cyclotomic=check_divisor_criterion(),
                  proof_scope='The general stabilization theorem is analytic; finite checks certify the displayed example and algebraic identities.')
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('stabilization_certificates.json', json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],order8=result['sharp_example']['order8_center'],
                         least_smoothing_order=9,half_step_order=11,
                         falling_factorial_identities=result['polya']['coefficient_identities'],
                         cyclotomic=result['cyclotomic']),sort_keys=True))


if __name__ == '__main__':
    main()
