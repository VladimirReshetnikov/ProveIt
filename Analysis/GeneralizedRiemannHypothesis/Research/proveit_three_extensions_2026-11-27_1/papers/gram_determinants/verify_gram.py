#!/usr/bin/env python3
"""Exact certificates and finite illustrations for the degenerating Gram law.

Standard library only. The scalar certificate is exact. The weighted matrices
are explicit upper witnesses, not claims of finite optimality. No global
maximization of Psi is performed.
"""
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
import json


def totient(n):
    return sum(gcd(k, n) == 1 for k in range(1, n + 1))


def scalar_certificate():
    scale = 10**12
    lower = Fraction(0)
    upper = Fraction(0)
    rows = []
    for j in range(1, 11):
        s = 1024 - 9*j*j
        r = isqrt(s*scale*scale)
        assert r*r <= s*scale*scale < (r+1)*(r+1)
        coefficient = Fraction(16, 5*32**6) * Fraction(totient(j), j) * s*s
        lower += coefficient * Fraction(r, scale)
        upper += coefficient * Fraction(r+1, scale)
        rows.append({'j': j, 'totient': totient(j), 'radicand': s,
                     'sqrt_scaled_floor': r})
    target = Fraction(31839, 100000)
    assert lower > target > Fraction(71, 223)
    return {'T': '32/3', 'scale': scale, 'rows': rows,
            'lower': str(lower), 'upper': str(upper),
            'lower_decimal': float(lower), 'upper_decimal': float(upper),
            'certified_target': str(target),
            'comparison_to_pi': 'Uses the classical bound pi > 223/71.',
            'global_maximum_claimed': False}


def profile(s, amplitude, excluded=()):
    """R^2=s; T=32/3. Return primitive integer vectors with floor weights."""
    t2 = Fraction(1024, 9)
    excluded = set(excluded)
    data = []
    mh = (amplitude*(1-t2/(s*s))).__floor__()
    if mh > 0 and (1, 0) not in excluded:
        data.append([1, 0, mh])
    for j in range(1, 11):
        bound2 = Fraction(s*s)*(t2-j*j)/(t2*t2)
        b = isqrt(bound2.numerator//bound2.denominator)
        assert Fraction(b*b) <= bound2 < Fraction((b+1)*(b+1))
        for u in range(-b, b+1):
            if gcd(u, j) != 1 or (u, j) in excluded:
                continue
            g = 1-Fraction(j*j)/t2-t2*Fraction(u*u, s*s)
            m = (amplitude*g).__floor__()
            if m > 0:
                data.append([u, j, m])
    return data


def statistics(data, check_cauchy_binet=False):
    assert len({(x,y) for x,y,m in data}) == len(data)
    assert all(m > 0 and gcd(x,y) == 1 for x,y,m in data)
    n = sum(m for x,y,m in data)
    q = sum(m*m for x,y,m in data)
    z = sum(m*(m-1)//2 for x,y,m in data)
    assert q == n+2*z
    a = sum(m*x*x for x,y,m in data)
    b = sum(m*x*y for x,y,m in data)
    c = sum(m*y*y for x,y,m in data)
    energy = a*c-b*b
    assert energy > 0
    # A primitive horizontal column and any row-one vector prove gcd 1.
    assert any((x,y)==(1,0) for x,y,m in data)
    assert any(y==1 for x,y,m in data)
    if check_cauchy_binet:
        total = 0
        pair_zero = sum(m*(m-1)//2 for x,y,m in data)
        for i,(x,y,m) in enumerate(data):
            for u,v,k in data[:i]:
                det = x*v-y*u
                assert det != 0
                total += m*k*det*det
        assert total == energy
        assert pair_zero == z
    ratio = Fraction(energy*z*z, n**6)
    return {'columns': n, 'distinct_directions': len(data),
            'zero_minors': z, 'squared_multiplicity_sum': q,
            'gram': [[a,b],[b,c]], 'gcd_maximal_minors': 1,
            'normalized_gram_determinant': energy,
            'scaled_ratio_E_z2_n6': str(ratio),
            'scaled_ratio_decimal': float(ratio),
            'z_over_n': z/n, 'z_over_n2': z/(n*n)}


def four_squares(n):
    two = {}
    b = isqrt(n)
    for a in range(b+1):
        for c in range(isqrt(n-a*a)+1):
            two.setdefault(a*a+c*c, (a,c))
    for s, pair in two.items():
        if n-s in two:
            ans = pair+two[n-s]
            assert sum(x*x for x in ans) == n
            return ans
    raise AssertionError('Lagrange four-square representation not found')


def exact_repair_certificate():
    reserved = [(u,1) for u in range(8)]
    bulk = profile(200, 200, excluded=reserved)
    before = statistics(bulk, True)
    residual = 1357
    m = 40
    assert residual <= m*m
    xs = four_squares(residual)
    after_data = list(bulk)
    additions = []
    for j,x in enumerate(xs):
        assert x <= m
        additions += [[2*j,1,m+x],[2*j+1,1,m-x]]
    additions = [row for row in additions if row[2] > 0]
    after_data += additions
    after = statistics(after_data, True)
    expected_n = before['columns']+8*m
    expected_z = before['zero_minors']+4*m*(m-1)+residual
    assert after['columns'] == expected_n
    assert after['zero_minors'] == expected_z
    return {'bulk_parameters': {'R_squared': 200, 'amplitude': 200, 'T':'32/3'},
            'M': m, 'residual': residual, 'four_squares': list(xs),
            'bulk_statistics': before, 'final_statistics': after,
            'reserved_columns': additions, 'full_weighted_matrix': after_data,
            'exact_target_n': expected_n, 'exact_target_z': expected_z}


def main():
    out = Path(__file__).resolve().parent / 'data'
    out.mkdir(exist_ok=True)
    scalar = scalar_certificate()
    examples = []
    for s in [100, 300, 1000, 3000, 10000]:
        data = profile(s,s)
        result = statistics(data, check_cauchy_binet=(s<=300))
        result['R_squared'] = s
        result['amplitude'] = s
        examples.append(result)
    repair = exact_repair_certificate()
    report = {'scalar_certificate': scalar,
              'profile_examples': examples,
              'exact_count_repair': repair,
              'scope': 'Exact finite checks; no finite optimality or global scalar maximizer claim.'}
    (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    lines = [
        'Exact rational scalar certificate passed.',
        f"Psi(32/3) in [{scalar['lower_decimal']:.15f}, {scalar['upper_decimal']:.15f}].",
        'Certified Psi(32/3) > 31839/100000 > 71/223 > 1/pi.',
        'The final comparison uses Archimedes\' classical lower bound pi > 223/71.',
        '', 'Explicit primitive weighted matrices (upper witnesses only):',
        'R^2  columns  zero_minors  distinct  E*z^2/n^6',
    ]
    for e in examples:
        lines.append(f"{e['R_squared']:5d}  {e['columns']:12d}  {e['zero_minors']:16d}  {e['distinct_directions']:6d}  {e['scaled_ratio_decimal']:.12f}")
    lines += ['', 'Exact four-square repair passed.',
              f"Residual {repair['residual']} = sum of squares of {repair['four_squares']}.",
              f"Final exact columns: {repair['exact_target_n']}; exact zero minors: {repair['exact_target_z']}.",
              'Cauchy--Binet, integer Gram entries, zero-minor counts, and gcd-one witnesses passed.',
              'No global scalar maximum or finite matrix optimum is asserted.']
    text = '\n'.join(lines)+'\n'
    (out/'verification.txt').write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()
