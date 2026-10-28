#!/usr/bin/env python3
"""Reusable annulus Cauchy modes and exact verification.

Public helpers: orderings(max_i, count), r_feature(z,b,points),
s_feature(j,b,points), and count_weighted_tuples(weights,precision).
Run ``python code/annulus_modes.py`` from the package root to regenerate
results/annulus_checks.json. The module is safe to import: checks run only
when explicitly requested through main() or command-line execution.

Exact finite checks for the annulus Cauchy-mode lemmas.

This validates the delivered algebra and finite examples, not the full SAT
algorithm or its asymptotic runtime. Python standard library only. All
identities are exact rational or modular identities; no floating point.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json


def require(condition, label):
    """A verification gate that remains active under python -O."""
    if not condition:
        raise RuntimeError(label)


def v2(x):
    if isinstance(x, Fraction):
        if not x:
            return 10**9
        return v2(x.numerator) - v2(x.denominator)
    if not x:
        return 10**9
    x = abs(x)
    return (x & -x).bit_length() - 1


def vf(b):
    return b - b.bit_count()


def orderings(max_i, count):
    """Return exact point/valuation arrays; odd branch wins a tie."""
    points = [[2*b+1 for b in range(count)]]
    costs = [[b+vf(b) for b in range(count)]]
    for i in range(1, max_i+1):
        a, f = [], []
        no = ne = 0
        for b in range(count):
            co = no+vf(no)
            ce = ne+costs[-1][ne]
            if co <= ce:
                a.append(2*no+1)
                f.append(co)
                no += 1
            else:
                a.append(2*points[-1][ne])
                f.append(ce)
                ne += 1
        points.append(a)
        costs.append(f)
    return points, costs


def r_feature(z, b, points):
    """Exact rational target feature for a supplied ordering prefix."""
    ans = Fraction(factorial(b))
    for h in range(b):
        ans *= z-2*points[h]
    for h in range(b+1):
        ans /= 1-h*z
    return ans


def s_feature(j, b, points):
    """Exact integral source feature, with integer binomial evaluation."""
    if j < b:
        return Fraction(0)
    ans = Fraction((1-2*b*points[b])*comb(j,b))
    for h in range(b+1):
        ans /= 1-2*points[h]*j
    return ans


def count_weighted_tuples(weights, precision):
    """Count nonnegative exponent tuples with weighted sum < precision.

    This is an exact abstract mode-budget count, without any additional
    network degree restrictions. Repeated weights represent distinct modes.
    """
    require(isinstance(precision, int) and precision >= 1,
            'precision must be a positive integer')
    require(all(isinstance(w, int) and w >= 1 for w in weights),
            'every mode weight must be a positive integer')
    coefficients = [0] * precision
    coefficients[0] = 1
    for weight in weights:
        for total in range(weight, precision):
            coefficients[total] += coefficients[total-weight]
    return sum(coefficients)


class UnramifiedF4:
    """(Z/2^p Z)[U]/(U^2+U+1), with exact modular pair arithmetic."""
    def __init__(self, precision):
        self.precision = precision
        self.modulus = 1 << precision

    def scalar(self, x):
        return (x % self.modulus, 0)

    def add(self, x, y):
        return ((x[0]+y[0]) % self.modulus,
                (x[1]+y[1]) % self.modulus)

    def sub(self, x, y):
        return ((x[0]-y[0]) % self.modulus,
                (x[1]-y[1]) % self.modulus)

    def mul(self, x, y):
        a,b = x
        c,d = y
        return ((a*c-b*d) % self.modulus,
                (a*d+b*c-b*d) % self.modulus)

    def inv(self, x):
        a,b = x
        norm = (a*a-a*b+b*b) % self.modulus
        if norm % 2 == 0:
            raise ValueError('attempted inversion of a nonunit')
        inv_norm = pow(norm, -1, self.modulus)
        return (((a-b)*inv_norm) % self.modulus,
                (-b*inv_norm) % self.modulus)

    def valuation(self, x):
        return min(self.precision, v2(x[0]), v2(x[1]))

    def rational(self, x):
        x = Fraction(x)
        if x.denominator % 2 == 0:
            raise ValueError('nonintegral rational')
        return self.scalar(x.numerator*pow(x.denominator,-1,self.modulus))


def main():
    points, costs = orderings(9, 97)
    stats = {
        'ordering_parameter_cases': 0,
        'minimum_candidate_products': 0,
        'rational_feature_weight_checks': 0,
        'rational_kernel_identities': 0,
        'unramified_feature_weight_checks': 0,
        'unramified_kernel_identities': 0,
        'exact_feature_dominance_checks': 0,
    }
    # Recurrence, selected-point minimality, finite exhaustive comparison,
    # point bound, and rational (weaker rounded-log) slope bounds.
    for i in range(10):
        slope = Fraction(1) + Fraction(3, 4**(i+1)-1)
        for b in range(97):
            aa = points[i]
            ff = costs[i]
            require(aa[b] <= 2 * b + 1, 'check at source line 131: aa[b] <= 2 * b + 1')
            require(v2(aa[b]) <= i, 'check at source line 132: v2(aa[b]) <= i')
            require(len(set(aa[:b + 1])) == b + 1, 'check at source line 133: len(set(aa[:b + 1])) == b + 1')
            require(ff[b] >= vf(b), 'check at source line 134: ff[b] >= vf(b)')
            require(ff[b] <= slope * b, 'check at source line 135: ff[b] <= slope * b')
            ceil_log = (b+1).bit_length()
            require(ff[b] >= slope * b - 4 * ceil_log, 'check at source line 137: ff[b] >= slope * b - 4 * ceil_log')
            selected_cost = sum(v2(aa[b]-a) for a in aa[:b])
            require(selected_cost == ff[b], 'check at source line 139: selected_cost == ff[b]')
            candidates = [x for x in range(1, 4*97+2)
                          if v2(x) <= i and x not in aa[:b]]
            brute_min = min(sum(v2(x-a) for a in aa[:b])
                            for x in candidates)
            stats['minimum_candidate_products'] += len(candidates)
            require(brute_min == ff[b], 'check at source line 145: brute_min == ff[b]')
            stats['ordering_parameter_cases'] += 1

    # Actual row parameters from the original packet geometry. T belongs
    # to Z_(2) here; nonzero extension coordinates are checked below.
    for i in range(4):
        for a in range(i+2, i+5):
            L = 1 << a
            alpha = 1 << (a+1)
            J = 1 << (a-i-1)
            R = a+1-i
            for sign in (-1,1):
                t = sign*(1 << i)
                for zeta in (Fraction(1), Fraction(-1), Fraction(1,3)):
                    T = t+alpha*zeta
                    # All rows/tiles for L<=16; representative rows above it.
                    row_values = range(L) if L <= 16 else sorted({0,1,L//3,L//2,L-1})
                    for x in row_values:
                        for y0 in range(1 << (i+1)):
                            if ((x >> i)&1) != ((y0 >> i)&1):
                                continue
                            d0 = t-y0+x
                            require(v2(d0) <= i, 'check at source line 167: v2(d0) <= i')
                            d = T-y0+x
                            z = Fraction(1 << (i+1), 1)/d
                            w0 = Fraction(1 << i, d0)
                            require(v2(z / 2 - w0) >= R, 'check at source line 171: v2(z / 2 - w0) >= R')
                            rr = [r_feature(z,b,points[i]) for b in range(J)]
                            for b,r in enumerate(rr):
                                bound = b+costs[i][b]+vf(b)
                                require(v2(r) >= bound, 'check at source line 175: v2(r) >= bound')
                                require(bound >= b + 2 * vf(b), 'check at source line 176: bound >= b + 2 * vf(b)')
                                stats['rational_feature_weight_checks'] += 1
                                stats['exact_feature_dominance_checks'] += 1
                            for j in range(J):
                                actual = sum((rr[b]*s_feature(j,b,points[i])
                                              for b in range(J)), Fraction(0))
                                expected = Fraction(1)/(1-z*j)
                                require(actual == expected, 'check at source line 183: actual == expected')
                                stats['rational_kernel_identities'] += 1

    # Verify the finite-precision integrality argument in a nontrivial
    # unramified extension, so the rows are not merely rational numbers.
    ring = UnramifiedF4(160)
    one = ring.scalar(1)
    for i in range(4):
        for a in range(i+2, i+5):
            L = 1 << a
            alpha = 1 << (a+1)
            J = 1 << (a-i-1)
            for t in (-(1 << i),1 << i):
                for zeta in ((0,1),(1,1),(3,2)):
                    for x in sorted({0,1,L//3,L-1}):
                        for y0 in range(1 << (i+1)):
                            if ((x >> i)&1) != ((y0 >> i)&1):
                                continue
                            d0 = t-y0+x
                            e = v2(d0)
                            require(e <= i, 'check at source line 203: e <= i')
                            d_unit = ((d0+alpha*zeta[0])//(1 << e),
                                      (alpha*zeta[1])//(1 << e))
                            z = ring.mul(ring.scalar(1 << (i+1-e)),
                                         ring.inv(d_unit))
                            rr = []
                            for b in range(J):
                                r = ring.scalar(factorial(b))
                                for h in range(b):
                                    r = ring.mul(r,ring.sub(z,ring.scalar(2*points[i][h])))
                                for h in range(b+1):
                                    den = ring.sub(one,ring.mul(ring.scalar(h),z))
                                    r = ring.mul(r,ring.inv(den))
                                rr.append(r)
                                require(ring.valuation(r) >= b + costs[i][b] + vf(b), 'check at source line 217: ring.valuation(r) >= b + costs[i][b] + vf(b)')
                                stats['unramified_feature_weight_checks'] += 1
                            for j in range(J):
                                actual = ring.scalar(0)
                                for b in range(J):
                                    sf = ring.rational(s_feature(j,b,points[i]))
                                    actual = ring.add(actual,ring.mul(rr[b],sf))
                                expected = ring.inv(ring.sub(one,ring.mul(ring.scalar(j),z)))
                                require(actual == expected, 'check at source line 225: actual == expected')
                                stats['unramified_kernel_identities'] += 1

    # Concrete, exact pruning comparison for one abstract tile family.
    # The geometry a=i+5 gives R=6 and J=16 at each displayed level.
    tuple_table = []
    expected_new = [634, 1421, 1683, 1723]
    for i in range(4):
        old_weights = [6+b+2*vf(b) for b in range(16)]
        new_weights = [6+b+costs[i][b]+vf(b) for b in range(16)]
        old_count = count_weighted_tuples(old_weights,64)
        new_count = count_weighted_tuples(new_weights,64)
        require(old_count == 1726, 'matched old tuple count changed')
        require(new_count == expected_new[i], 'annulus tuple count changed')
        require(new_count < old_count, 'expected strict local pruning')
        tuple_table.append({'valuation_level':i, 'packet_exponent':i+5,
                            'base_weight_R':6, 'tile_length_J':16,
                            'precision_exclusive':64, 'families':1,
                            'old_tuple_count':old_count,
                            'annulus_tuple_count':new_count})
    stats['abstract_tuple_comparison'] = tuple_table
    stats['abstract_tuple_scope'] = ('Exact enumeration under the mode-weight '
                                    'budget only; these are not SAT runtimes '
                                    'or counts for complete contraction instances.')

    # Negative control: extension rows without the prime-subring proximity
    # assumption need not satisfy the stronger annulus divisibility.
    # For z=2U, i=0, b=1 the target feature has valuation one, below the
    # (inapplicable) bound 1+F_0(1)=2. This row is outside the theorem domain.
    z_outside = (0,2)
    r_outside = ring.mul(ring.sub(z_outside,ring.scalar(2)),
                         ring.inv(ring.sub(one,z_outside)))
    outside_valuation = ring.valuation(r_outside)
    invalid_bound = 1+costs[0][1]+vf(1)
    require(outside_valuation == 1 and invalid_bound == 2,
            'outside-domain negative control changed')
    require(outside_valuation < invalid_bound,
            'outside-domain negative control failed to refute invalid extension')
    guard_rejected = False
    try:
        require(False, 'intentional verification-gate negative control')
    except RuntimeError:
        guard_rejected = True
    require(guard_rejected, 'verification gate failed to reject False')
    stats['negative_controls'] = {
        'explicit_false_gate_rejected':guard_rejected,
        'arbitrary_extension_row':{
            'row':'z=2U in the quadratic unramified extension',
            'valuation_level':0, 'mode_index':1,
            'actual_target_feature_valuation':outside_valuation,
            'inapplicable_annulus_bound':invalid_bound,
            'invalid_generalization_rejected':True,
            'reason':'z/2=U is not close to an ordinary two-integral odd rational'
        }
    }
    stats['optimization_scope'] = (
        'All verification gates are explicit require/RuntimeError calls and '
        'remain active under python -O. Separate normal and optimized execution '
        'reports and their comparison are in annulus_execution_validation.json.')

    stats['status'] = 'PASS'
    stats['arithmetic'] = 'exact fractions and exact arithmetic modulo 2^160'
    stats['scope'] = ('Checks the new local ordering, integral feature bounds, '
                      'and Cauchy identities; not a full SAT implementation, '
                      'proof-assistant formalization, or runtime benchmark.')
    stats['first_costs'] = {str(i): costs[i][:17] for i in range(4)}
    stats['first_points'] = {str(i): points[i][:17] for i in range(4)}
    stats['slopes'] = {str(i): str(Fraction(3)+Fraction(3,4**(i+1)-1))
                       for i in range(5)}
    output = Path(__file__).resolve().parents[1] / 'results' / 'annulus_checks.json'
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))


if __name__ == '__main__':
    main()
