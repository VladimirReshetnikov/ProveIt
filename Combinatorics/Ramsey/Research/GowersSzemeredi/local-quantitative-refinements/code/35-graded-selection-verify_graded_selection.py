#!/usr/bin/env python3
"""Independent exact finite diagnostics for the graded arrangement selector.

This check enumerates coefficient arrays, field seeds,
and actual physical-vertex inclusion events. It is not a proof assistant.
Only the Python standard library is used.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json


def dot(a, b, p):
    return sum(x*y for x, y in zip(a, b)) % p


def degree_one_checks():
    p, m, k, L = 3, 4, 1, 2
    s = m*2**k
    sigma = (1, 1, -1, -1)
    eta0 = tuple(z for sig in sigma for z in (sig, -sig))
    levels = tuple(r+(sum(sig*x for sig, x in zip(sigma[:-1], r)) % p,)
                   for r in product(range(p), repeat=m-1))
    denom = p**(2*m-1)  # h fixed nonzero; all x and admissible r.
    mass = {0: F(0), 1: F(0)}
    weighted_success = F(0)
    counts = {0: 0, 1: 0}
    maximum = {0: F(0), 1: F(0)}
    sharp_examples = {}
    zero_probability_patterns = 0
    for eta in product((-1, 0, 1), repeat=s):
        weight = F(2**eta.count(0), 4**s)
        A = tuple((eta[2*j]+eta[2*j+1]) % p for j in range(m))
        B = tuple(eta[2*j+1] % p for j in range(m))
        t = 1 if any(A) else 0
        feasible_balance = (sum(A) % p == 0 if t else sum(B) % p == 0)
        if feasible_balance:
            mass[t] += weight
        universal = any(all((a-lam*b) % p == 0 for a, b in zip(eta, eta0))
                        for lam in range(p))
        if universal:
            continue
        counts[t] += 1
        solutions = 0
        if sum(A) % p == 0:
            rhs1 = -sum(B) % p
            pivot = next((j for j, value in enumerate(A) if value), None)
            for r in levels:
                if dot(A, r, p):
                    continue
                rhs2 = -dot(B, r, p) % p
                if pivot is None:
                    if rhs1 == 0 and rhs2 == 0:
                        solutions += p**m
                    continue
                row2 = tuple(a*rr % p for a, rr in zip(A, r))
                lam = row2[pivot] * pow(A[pivot], -1, p) % p
                if all((v-lam*a) % p == 0 for v, a in zip(row2, A)):
                    if rhs2 == lam*rhs1 % p:
                        solutions += p**(m-1)
                else:
                    solutions += p**(m-2)
        probability = F(solutions, denom)
        bound = F(1, p) if t == 0 else F(1, p*p)+F(p-1, p**m)
        assert probability <= bound, (eta, t, probability, bound)
        if not feasible_balance:
            assert probability == 0
        if probability == 0:
            zero_probability_patterns += 1
        if probability > maximum[t]:
            maximum[t] = probability
            sharp_examples[t] = eta
        weighted_success += weight*probability
    for t in (0, 1):
        c = sum(comb(k, i) for i in range(t+1))
        D = m*c-comb(k, t)
        assert mass[t] <= F(1, L)**(s-D)
    weighted_bound = F(1, 2)**5*F(1, 3)+F(1, 2)*(F(1, 9)+F(2, 81))
    assert weighted_success <= weighted_bound
    assert maximum[0] == F(1, 3)
    assert maximum[1] == F(11, 81)
    return {
        'p': p, 'm': m, 'k': k, 'L': L,
        'coefficient_arrays': 3**s,
        'nonuniversal_arrays_per_degree': counts,
        'zero_success_arrays': zero_probability_patterns,
        'eligible_product_mass_per_degree': mass,
        'max_success_probability_per_degree': maximum,
        'sharp_examples': sharp_examples,
        'weighted_nonuniversal_success': weighted_success,
        'weighted_upper_bound': weighted_bound,
    }


def actual_selector_checks():
    p, k, m, s, M = 3, 1, 4, 8, 8
    sigma = (1, 1, -1, -1)
    points = tuple(product(range(p), repeat=2))
    index = {point: i for i, point in enumerate(points)}
    phi = tuple(x*x*z % p for x, z in points)
    physical = {True: Counter(), False: Counter()}
    labeled = {True: Counter(), False: Counter()}
    bad_collision_count = 0
    bad_zero_side_count = 0
    for h in range(p):
        for xs in product(range(p), repeat=m):
            for first in product(range(p), repeat=m-1):
                zs = first+((first[0]+first[1]-first[2]) % p,)
                count = [0]*len(points)
                defect = 0
                for sig, x, z in zip(sigma, xs, zs):
                    left = index[(x, z)]
                    right = index[((x+h) % p, z)]
                    count[left] += 1
                    count[right] += 1
                    defect += sig*(phi[left]-phi[right])
                good = defect % p == 0
                mask = sum(1 << i for i, value in enumerate(count) if value)
                physical[good][mask] += 1
                labeled[good][tuple(count)] += 1
                if not good and mask.bit_count() < s:
                    bad_collision_count += 1
                    assert h != 0
                    collision_locus = any(
                        zs[j] == zs[ell]
                        and any((xs[ell]-xs[j]-delta*h) % p == 0
                                for delta in (-1, 0, 1))
                        for j in range(m) for ell in range(j+1, m))
                    assert collision_locus
                if not good and h == 0:
                    bad_zero_side_count += 1
    assert bad_zero_side_count == 0
    totals = {good: sum(hist.values()) for good, hist in physical.items()}
    assert sum(totals.values()) == p**M
    phys_numerator = {True: 0, False: 0}
    label_numerator = {True: 0, False: 0}
    point_means = [F(0)]*len(points)
    seed_count = p**5
    for u0, ux, uz, uxz, v in product(range(p), repeat=5):
        nonzero = tuple(int((u0+ux*x+uz*z+uxz*x*z+v*value) % p != 0)
                        for (x, z), value in zip(points, phi))
        badmask = sum(1 << i for i, value in enumerate(nonzero) if value)
        for i, value in enumerate(nonzero):
            point_means[i] += F(1, 4) if value else 1
        for good, hist in physical.items():
            phys_numerator[good] += sum(
                multiplicity*4**(len(points)-(mask & badmask).bit_count())
                for mask, multiplicity in hist.items())
        for good, hist in labeled.items():
            label_numerator[good] += sum(
                multiplicity*4**(s-sum(c*b for c, b in zip(count, nonzero)))
                for count, multiplicity in hist.items())
    point_means = [value/seed_count for value in point_means]
    assert all(value == F(1, 2) for value in point_means)
    actual = {good: F(value, seed_count*4**len(points))
              for good, value in phys_numerator.items()}
    label = {good: F(value, seed_count*4**s)
             for good, value in label_numerator.items()}
    scalar_weight = F(1, 2)**s+2*F(1, 4)**s
    assert label[True] >= scalar_weight*totals[True]
    for good in (False, True):
        assert actual[good] >= label[good]
    collision_gap = actual[False]-label[False]
    assert 0 < collision_gap <= F(bad_collision_count, 2)
    graded_label_bound = F(totals[False], 2**s) + p**M*(
        F(1, 2)**5*F(1, p)+F(1, 2)*(F(1, p*p)+F(p-1, p**m)))
    assert label[False] <= graded_label_bound
    Ccoll = comb(m, 2)*3**k
    assert bad_collision_count <= Ccoll*p**(M-k-1)
    return {
        'group': 'F_3^2', 'target_map': 'phi(x,z)=x^2 z',
        'arrangements': p**M, 'field_seeds': seed_count,
        'respected': totals[True], 'unrespected': totals[False],
        'physical_histogram_entries': sum(map(len, physical.values())),
        'labeled_histogram_entries': sum(map(len, labeled.values())),
        'each_point_mean': point_means[0],
        'actual_good_expectation': actual[True],
        'actual_bad_expectation': actual[False],
        'labeled_good_expectation': label[True],
        'labeled_bad_expectation': label[False],
        'good_scalar_lower_bound': scalar_weight*totals[True],
        'graded_bad_labeled_upper_bound': graded_label_bound,
        'bad_collision_count': bad_collision_count,
        'bad_collision_compensation_actually_needed': collision_gap,
        'collision_compensation_upper_bound': F(bad_collision_count, 2),
    }


def dimension_checks():
    # Count the necessary balance subspaces independently by enumeration
    # in coefficient coordinates for k=2, m=2; the dimension statement
    # itself does not require m>=4, unlike the success-probability theorem.
    p, k, m = 3, 2, 2
    results = []
    for t in range(k+1):
        monomials = tuple(mask for mask in range(2**k) if mask.bit_count() <= t)
        top = tuple(i for i, mask in enumerate(monomials) if mask.bit_count() == t)
        dimension = m*len(monomials)-len(top)
        accepted = 0
        for coefficients in product(range(p), repeat=m*len(monomials)):
            if all(sum(coefficients[j*len(monomials)+i] for j in range(m)) % p == 0
                   for i in top):
                accepted += 1
        assert accepted == p**dimension
        results.append({'k': k, 'm': m, 't': t, 'dimension': dimension,
                        'counted_subspace_size': accepted})
    return results


def table_checks():
    rows = []
    m = 16
    for k in range(1, 17):
        c = 0
        candidates = []
        for t in range(k+1):
            c += comb(k, t)
            D = m*c-comb(k, t)
            candidates.append((F(D, t+1), t, D))
        E, t, D = max(candidates)
        assert E >= F(m*2**k-1, k+1)
        assert E <= F(m*2**k-1, 2)
        rows.append({'k': k, 'm': m, 's': m*2**k, 'maximizing_t': t,
                     'D_at_maximum': D, 'E': E, 'old_Fejer_exponent': 2*m*2**k})
    return rows


def ceil_root_fraction(value, degree):
    lo, hi = 0, 1
    while hi**degree*value.denominator < value.numerator:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**degree*value.denominator >= value.numerator:
            hi = mid
        else:
            lo = mid
    return hi


def threshold_schedule_checks():
    checked = 0
    examples = []
    m = 4
    for k in range(1, 7):
        s = m*2**k
        C = comb(m, 2)*3**k
        dimensions = [m*sum(comb(k, i) for i in range(t+1))-comb(k, t)
                      for t in range(k+1)]
        for beta in (F(1), F(1, 2), F(2, 5)):
            for L in (2, 3, 5):
                a = [1+int(t == 1)+C*int(t == k) for t in range(k+1)]
                q = max(ceil_root_fraction(2*(k+1)*a[t]*beta**(-(m-1))*L**D,
                                           t+1)
                        for t, D in enumerate(dimensions))
                Q = [F(1, q**(t+1)) for t in range(k+1)]
                Q[1] += F(q-1, q**m)
                budget = sum(L**D*prob for D, prob in zip(dimensions, Q))
                budget += F(C*L**(s-1), q**(k+1))
                assert budget <= beta**(m-1)/2
                checked += 1
                if beta == F(1, 2) and L == 3:
                    examples.append({'k': k, 'm': m, 'L': L, 'beta': beta,
                                     'integer_q_bound': q,
                                     'normalized_budget': budget/beta**(m-1)})
    return {'exact_schedules_checked': checked, 'examples': examples}


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serializable(x) for x in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='write the complete JSON record to this path')
    args = parser.parse_args()
    result = {
        'coefficient_rank_checks': degree_one_checks(),
        'actual_subset_selector_checks': actual_selector_checks(),
        'balance_subspace_dimension_checks': dimension_checks(),
        'threshold_exponent_table': table_checks(),
        'threshold_schedule_checks': threshold_schedule_checks(),
        'status': 'PASS',
        'scope': 'Exact finite checks, not a general proof or Lean certification.',
    }
    output = json.dumps(serializable(result), indent=2)+'\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print('Passed all exact coefficient, subset-selection, dimension, and threshold checks.')
    print('Coefficient arrays: 6,561; arrangements: 6,561; field seeds: 243.')
    print('Exact threshold schedules: 54.')


if __name__ == '__main__':
    main()
