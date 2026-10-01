#!/usr/bin/env python3
"""Exact finite audits of the affine paired-SL2 subgroup-input obstruction.

The proof is algebraic, not inferred from finite testing.  There is no
Diophantine operation lower bound and no assertion for general SL3 curves.
"""
import argparse
from itertools import product
import json
from math import gcd
from pathlib import Path
import random


I = (1, 0, 0, 1)
ZERO = (0, 0, 0, 0)
U = (1, 1, 0, 1)
V = (1, 0, 1, 1)
J = (0, -1, 1, 0)


def multiply(a, b):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))
                 for i in range(2) for j in range(2))


def determinant(a):
    return a[0]*a[3]-a[1]*a[2]


def inverse(a):
    assert determinant(a) == 1
    return (a[3], -a[1], -a[2], a[0])


def power(a, exponent):
    if exponent < 0:
        a, exponent = inverse(a), -exponent
    result = I
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent //= 2
    return result


def affine(c, d, x):
    return tuple(a+x*b for a, b in zip(c, d))


def coefficients(c, d):
    """Coefficients of det(C+xD), in increasing degree."""
    return (determinant(c), c[0]*d[3]+d[0]*c[3]-c[1]*d[2]-d[1]*c[2],
            determinant(d))


def factor_curve(c, d):
    assert coefficients(c, d) == (1, 0, 0)
    n = multiply(inverse(c), d)
    assert n[0]+n[3] == 0 and determinant(n) == 0
    assert multiply(n, n) == ZERO
    p = affine(I, n, 1)
    assert inverse(p) == affine(I, n, -1)
    return n, p


def paired_multiply(left, right):
    return tuple(multiply(a, b) for a, b in zip(left, right))


def paired_power(value, exponent):
    return tuple(power(a, exponent) for a in value)


def paired_inverse(value):
    return tuple(inverse(a) for a in value)


def integral_curve_checks():
    matrices = list(product(range(-2, 3), repeat=4))
    constants = [c for c in matrices if determinant(c) == 1]
    candidates = valid = power_checks = noncommuting = 0
    for c, d in product(constants, matrices):
        candidates += 1
        # Three exact values determine this degree-at-most-two polynomial.
        sampled = all(determinant(affine(c, d, x)) == 1 for x in (-1, 0, 1))
        assert sampled == (coefficients(c, d) == (1, 0, 0))
        if not sampled:
            continue
        n, p = factor_curve(c, d)
        noncommuting += multiply(c, p) != multiply(p, c)
        for x in range(-8, 9):
            assert power(p, x) == affine(I, n, x)
            assert affine(c, d, x) == multiply(c, power(p, x))
            power_checks += 1
        valid += 1
    assert noncommuting > 0
    return dict(candidate_affine_curves=candidates, valid_determinant_one_curves=valid,
                integral_power_identity_checks=power_checks,
                noncommuting_constant_power_factors=noncommuting,
                coordinate_box=[-2, 2], exponent_range=[-8, 8])


def reduce_pair(value, modulus):
    return tuple(tuple(entry % modulus for entry in matrix) for matrix in value)


def finite_multiply(left, right, modulus):
    return reduce_pair(paired_multiply(left, right), modulus)


def finite_inverse(value, modulus):
    # The residue determinant is 1 modulo m, so use the adjugate directly.
    return tuple((a[3] % modulus, -a[1] % modulus,
                  -a[2] % modulus, a[0] % modulus) for a in value)


def finite_subgroup(generators, modulus):
    identity = (I, I)
    alphabet = tuple(reduce_pair(g, modulus) for g in generators)
    alphabet += tuple(finite_inverse(g, modulus) for g in alphabet)
    reached, frontier = {identity}, [identity]
    while frontier:
        current = frontier.pop()
        for generator in alphabet:
            following = finite_multiply(current, generator, modulus)
            if following not in reached:
                reached.add(following)
                frontier.append(following)
    return reached


def finite_quotient_checks():
    rng = random.Random(206051)
    constants = [c for c in product(range(-2, 3), repeat=4) if determinant(c) == 1]
    nilpotents = [n for n in product(range(-2, 3), repeat=4)
                 if n[0]+n[3] == 0 and determinant(n) == 0]
    fixtures = exponent_checks = quotient_identity_checks = noncommuting = 0
    outcomes = {'empty': 0, 'all': 0, 'proper_progression': 0}
    periods = set()
    for modulus in (2, 3, 4):
        for case in range(36):
            c = tuple(rng.choice(constants) for _ in range(2))
            n = tuple(rng.choice(nilpotents) for _ in range(2))
            p = tuple(affine(I, block, 1) for block in n)
            d = tuple(multiply(a, b) for a, b in zip(c, n))
            base = rng.randrange(-4, 5)
            selected = paired_multiply(c, paired_power(p, base))
            generators = (() if case % 4 == 0 else
                          (selected,) if case % 4 == 1 else
                          (selected, paired_power(p, 2)) if case % 4 == 2 else
                          tuple(tuple(rng.choice(constants) for _ in range(2)) for _ in range(2)))
            subgroup = finite_subgroup(generators, modulus)
            accepted = {x for x in range(modulus)
                        if reduce_pair(tuple(affine(a, b, x) for a, b in zip(c, d)), modulus) in subgroup}
            differences = {x for x in range(modulus)
                           if reduce_pair(paired_power(p, x), modulus) in subgroup}
            period = modulus
            for x in differences:
                period = gcd(period, x)
            assert differences == {x for x in range(modulus) if x % period == 0}
            if accepted:
                x0 = min(accepted)
                assert accepted == {(x0+x) % modulus for x in differences}
                outcome = 'all' if len(accepted) == modulus else 'proper_progression'
                periods.add(period)
            else:
                x0, outcome = None, 'empty'
            outcomes[outcome] += 1
            noncommuting += paired_multiply(c, p) != paired_multiply(p, c)
            for x in range(-12, 13):
                target = tuple(affine(a, b, x) for a, b in zip(c, d))
                assert target == paired_multiply(c, paired_power(p, x))
                actual = reduce_pair(target, modulus) in subgroup
                assert actual == (x0 is not None and (x-x0) % period == 0)
                if x0 is not None:
                    start = paired_multiply(c, paired_power(p, x0))
                    # Left quotient, with no illicit commutation past C.
                    assert paired_multiply(paired_inverse(start), target) == paired_power(p, x-x0)
                    quotient_identity_checks += 1
                exponent_checks += 1
            fixtures += 1
    assert all(outcomes.values()) and noncommuting > 0 and 2 in periods
    return dict(paired_affine_fixtures=fixtures, membership_exponents_checked=exponent_checks,
                exact_left_quotient_identities=quotient_identity_checks,
                noncommuting_factor_fixtures=noncommuting,
                moduli=[2, 3, 4], observed_positive_periods=sorted(periods), outcomes=outcomes,
                scope='Each subgroup is the inverse image of an explicitly enumerated subgroup '
                      'of SL2(Z/mZ) x SL2(Z/mZ). Membership is exact, not a finite-word search cutoff.')


def explicit_cases():
    powers_j = {power(J, i) for i in range(4)}
    outcomes = {'empty': 0, 'all': 0, 'progression': 0, 'singleton': 0, 'coupled_singleton': 0}
    for x in range(-16, 17):
        # All: a constant identity target in the trivial subgroup.
        assert affine(I, ZERO, x) in {I}
        outcomes['all'] += 1
        # Empty: J U^x has lower-left entry 1; <U> has lower-left 0.
        empty_target = multiply(J, power(U, x))
        assert empty_target[2] == 1
        outcomes['empty'] += 1
        # Progression: U^(x-2) belongs to <U^5> precisely for x=2 mod5.
        target = power(U, x-2)
        in_u5 = target[0] == target[3] == 1 and target[2] == 0 and target[1] % 5 == 0
        assert in_u5 == ((x-2) % 5 == 0)
        outcomes['progression'] += 1
        # Singleton: J U^(x-3) belongs to the finite subgroup <J> only at3.
        singleton = multiply(J, power(U, x-3))
        assert (singleton in powers_j) == (x == 3)
        outcomes['singleton'] += 1
        # Both blocks individually lie in the respective cyclic projections,
        # but the coupled subgroup requires matching their exponents.
        left, right = power(U, x), power(V, 2*x-3)
        assert left[1] == x and right[2] == 2*x-3
        assert (left[1] == right[2]) == (x == 3)
        outcomes['coupled_singleton'] += 1
    # The important noncommutation failure if the factors are reversed.
    c, p = V, U
    assert multiply(c, p) != multiply(p, c)
    assert multiply(inverse(multiply(c, power(p, 2))), multiply(c, power(p, 5))) == power(p, 3)
    return dict(exponent_range=[-16, 16], exact_case_checks=outcomes,
                singleton_subgroup='<J>, J=[[0,-1],[1,0]], exact order4',
                coupled_subgroup='{(U^n,V^n): n in Z}',
                scope='The displayed entry formulas give exact membership oracles for these infinite/finite subgroups.')


def higher_rank_boundary():
    def multiply3(a, b):
        return tuple(sum(a[3*i+k]*b[3*k+j] for k in range(3))
                     for i in range(3) for j in range(3))
    i3 = (1, 0, 0, 0, 1, 0, 0, 0, 1)
    n = (0, 1, 0, 0, 0, 1, 0, 0, 0)
    n2 = multiply3(n, n)
    assert n2 != (0,)*9 and multiply3(n2, n) == (0,)*9
    p = tuple(a+b for a, b in zip(i3, n))
    assert multiply3(p, p) != tuple(a+2*b for a, b in zip(i3, n))
    matches = []
    for x in range(-12, 13):
        target = tuple(a+(x-1)*b for a, b in zip(i3, n))
        # Equality to P^e forces e=x-1 by entry(1,2); entry(1,3)
        # then forces e(e-1)/2=0.  This tests the exact forced exponent.
        e = x-1
        candidate = tuple(a+e*b+e*(e-1)//2*c for a, b, c in zip(i3, n, n2))
        if target == candidate:
            matches.append(x)
    assert matches == [1, 2]
    return dict(nilpotency_index_three_counterexample=True,
                affine_SL3_target='I+(x-1)N, N=E12+E23',
                subgroup='<I+N>', exact_integer_membership_set=[1, 2],
                scope='This explicit counterexample prevents extending the affine-SL2 classification to all SL3 curves.')


def verify():
    return dict(status='PASS_GROUP_AFFINE_INPUT_OBSTRUCTION',
                scalar=integral_curve_checks(), paired_finite_quotients=finite_quotient_checks(),
                exact_examples=explicit_cases(), higher_rank_boundary=higher_rank_boundary(),
                theorem='For one or two entrywise-affine integer SL2 blocks and any fixed subgroup, '
                        'the integer membership set is empty or x0+dZ, d>=0; d=0 means a singleton.',
                consequence='Degree at least2 is necessary for a paired-SL2 polynomial input curve '
                            'to represent every computably enumerable positive set via fixed subgroup membership.',
                limits='This is an input-interface degree obstruction, not an arithmetic-operation or '
                       'Diophantine-witness lower bound. Fixed subgroup is essential; general SL3 targets '
                       'are explicitly outside the theorem. No computational universality theorem is inferred from finite tests.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print('Affine paired-SL2 subgroup input gives only empty sets, singleton sets, or one arithmetic progression.')
