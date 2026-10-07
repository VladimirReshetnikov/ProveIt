#!/usr/bin/env python3
"""Exact finite certificates for two-harmonic real U4/U2 norm gaps.

Python standard library only. No floating point enters a mathematical check.
The output JSON gives all integer dual-polynomial coefficient tables and
rational bounds. Running this file regenerates every certificate from finite
Fourier orthogonality, instead of trusting precomputed polynomial data.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use python -O or -OO.')

V3 = list(product((0, 1), repeat=3))
FREQUENCIES = (-3, -1, 1, 3)


def zero(value, order):
    return value == 0 if order is None else value % order == 0


def residue(value, order):
    return value if order is None else value % order


def enumerate_dual(order=None):
    """Return d[k][j] with D4(phi1+t phi3)=sum d_k(t) exp(ik theta) chi^k.

    Top face: eight vertices with fourth coordinate one; its frequencies sum
    to zero in the cyclic character group. Bottom: the seven nonzero vertices
    with fourth coordinate zero. Match the other three moments. Track the
    INTEGER total frequency (for phase dependence) and the number of +/-3's.
    """
    top = defaultdict(Counter)
    for fs in product(FREQUENCIES, repeat=8):
        total = sum(fs)
        if not zero(total, order):
            continue
        key = tuple(residue(sum(f*v[j] for f, v in zip(fs, V3)), order)
                    for j in range(3))
        degree = sum(abs(f) == 3 for f in fs)
        top[key][total, degree] += 1
    coefficients = defaultdict(Counter)
    for fs in product(FREQUENCIES, repeat=7):
        key = tuple(residue(-sum(f*v[j] for f, v in zip(fs, V3[1:])), order)
                    for j in range(3))
        subtotal = sum(fs)
        degree = sum(abs(f) == 3 for f in fs)
        for (total, k), count in top.get(key, {}).items():
            coefficients[subtotal+total][degree+k] += count
    assert 0 not in coefficients  # fifteen odd integers have odd total
    assert all(k % 2 for k in coefficients)
    assert all(dict(coefficients[k]) == dict(coefficients[-k])
               for k in coefficients)
    return coefficients


def evaluate(coefficients, t):
    return {k: sum((F(c)*t**j for j, c in polynomial.items()), F(0))
            for k, polynomial in coefficients.items() if k > 0}


def dual_bounds(coefficients, t, order):
    d = evaluate(coefficients, t)
    aliases = sum((abs(v) for k, v in d.items() if k != 1 and
                   (zero(k-1, order) or zero(k+1, order))), F(0))
    main = d[1] - aliases
    tail = sum((abs(v) for k, v in d.items() if not zero(k, order)
                and not zero(k-1, order) and not zero(k+1, order)), F(0))
    # P(theta)=sum P[l] cos(l theta), obtained as E g D4 g.
    cosine = defaultdict(F)
    for k, v in d.items():
        for j, a in ((1, F(1)), (3, t)):
            for sign in (-1, 1):
                frequency = k + sign*j
                if zero(frequency, order):
                    cosine[abs(frequency)] += 2*a*v
    upper = cosine[0] + sum((abs(v) for k, v in cosine.items() if k), F(0))
    assert main > 0 and upper > 0
    C = (2*main)**16/(16*upper**15)
    alpha = tail/main
    return dict(main=main, tail=tail, norm_upper=upper, C=C, alpha=alpha,
                norm_cosine=dict(cosine))


def profile(p):
    return F(35, 8)*(1 + 12*p*(1-p) + 6*p*p*(1-p)*(1-p))


def frac_tree(obj):
    if isinstance(obj, F):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): frac_tree(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [frac_tree(v) for v in obj]
    return obj


def main():
    output = {'description': __doc__, 'rows': {}}
    integer_coeff = enumerate_dual(None)
    assert sorted(k for k in integer_coeff if k > 0) == [1,3,5,7,9,11,13,15]
    expected_d1 = [111,405,1785,3705,9615,10934,17225,13860,
                   13090,6195,4530,665,740,0,0,0]
    assert [integer_coeff[1][j] for j in range(16)] == expected_d1
    # Compact rational table printed in the proof: lower main coefficient,
    # upper tail coefficient, and upper norm power, respectively.
    coarse = {
        None: (F(82255,1000), F(516,1000), F(164452,1000)),
        5: (F(82581,1000), F(389,1000), F(165863,1000)),
        7: (F(82256,1000), F(503,1000), F(164459,1000)),
        9: (F(82255,1000), F(509,1000), F(164452,1000)),
        11: (F(82255,1000), F(515,1000), F(164452,1000))}
    for order in (None, 5, 7, 9, 11):
        coeff = integer_coeff if order is None else enumerate_dual(order)
        t = F(-7, 50) if order == 5 else F(-1, 7)
        bound = dual_bounds(coeff, t, order)
        lo, hi_tail, hi_norm = coarse[order]
        assert bound['main'] > lo
        assert bound['tail'] < hi_tail
        assert bound['norm_upper'] < hi_norm
        coarse_C = (2*lo)**16/(16*hi_norm**15)
        coarse_alpha = hi_tail/lo
        if order == 5:
            assert coarse_C > F(242, 25)
            assert coarse_alpha < F(1, 200)
        else:
            assert coarse_C > F(1033, 100)
            assert coarse_alpha < F(63, 10000)
        # Independent normative polynomial check in the generic order case.
        if order is None:
            assert bound['norm_upper'] == F(5465198316262956, 7**16)
            assert list(bound['norm_cosine']) == [0]
        label = 'integer' if order is None else str(order)
        output['rows'][label] = {
            'order': label, 't': t, 'bounds': bound,
            'coarse_bounds': dict(main_lower=lo, tail_upper=hi_tail,
                                  norm_upper=hi_norm),
            'dual_coefficients': {k: [poly[j] for j in range(16)]
                                  for k, poly in sorted(coeff.items())}}
        print('order', label, 't', str(t), 'C', float(bound['C']),
              'alpha', float(bound['alpha']))

    # Explicit rational comparisons used by the proof; no decimal assumptions.
    assert F(1015,64) > F(15,2)
    assert profile(F(15,16)) == F(1976905,262144)
    assert profile(F(15,16)) > F(15,2)
    assert F(9839,10000)**4 < F(15,16)
    assert F(1033,100)*F(3923,4000)**16 > F(15,2)
    assert F(131,8)*F(15,16)**4 > F(15,2)
    assert profile(F(16,17)) > F(29,4)
    assert F(9849,10000)**4 < F(16,17)
    assert F(1,17) < F(1,2)**4
    assert F(9849,10000) - F(1,200)*F(1,2) == F(614,625)
    assert F(242,25)*F(614,625)**16 > F(29,4)
    assert F(131,8)*F(16,17)**4 > F(29,4)

    # Fifth-norm refinement from the same dual profile and the sixteenth
    # autocorrelation moment, at p=99/100.
    p = F(99,100)
    C8 = F(comb(16,8), 2**8)
    H8 = sum((F(comb(8,k)**2)*p**k*(1-p)**(8-k)
              for k in range(9)), F(0))
    assert C8*H8 > F(50,29)**8
    assert C8*(8-F(7,128)) > F(50,29)**8
    assert F(997,1000)**4 < F(99,100)
    assert F(8,25)**4 > F(1,100)
    assert F(997,1000)-F(63,10000)*F(8,25) == F(124373,125000)
    assert F(242,25)*F(124373,125000)**16 > F(50,29)**4

    # Recompute the order-three endpoint from the full Fourier cube.
    vertices = list(product((0,1), repeat=4))
    ternary = Counter()
    for fs in product((-1,1), repeat=16):
        if sum(fs) % 3:
            continue
        if any(sum(f*v[j] for f,v in zip(fs,vertices)) % 3
               for j in range(4)):
            continue
        ternary[sum(fs)] += 1
    assert dict(ternary) == {-12:8, -6:16, 0:286, 6:16, 12:8}
    output['order_three_full_cube'] = dict(ternary)
    output['rational_margins'] = {
        'high_order_moment': profile(F(15,16))-F(15,2),
        'high_order_dual': F(1033,100)*F(3923,4000)**16-F(15,2),
        'order_five_moment': profile(F(16,17))-F(29,4),
        'order_five_dual': F(242,25)*F(614,625)**16-F(29,4)}
    output['rational_margins']['fifth_norm_moment'] = C8*H8-F(50,29)**8
    output['rational_margins']['fifth_norm_dual'] = (
        F(242,25)*F(124373,125000)**16-F(50,29)**4)
    destination = Path(__file__).with_name('dual_gap_certificate.json')
    destination.write_text(json.dumps(frac_tree(output), indent=2)+'\n')
    digest = hashlib.sha256(destination.read_bytes()).hexdigest()
    print('All exact checks passed.')
    print('Certificate:', destination.name, 'SHA256:', digest)


if __name__ == '__main__':
    main()
