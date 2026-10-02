#!/usr/bin/env python3
"""Independent finite checks. These do not replace the article's infinite proofs."""
from __future__ import annotations
import json
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import comb, factorial
from pathlib import Path
from path_forests import (correction_polynomials, avoidance_coefficients,
    exact_distribution, stable_moments, forest_tilings, stable_F,
    profile_factorial, profile_coefficient, defect_profiles)

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    results = {}
    # OEIS A189281 and A110128 displayed values, inspected 1 October 2026.
    # These constants are used only for validation, never to generate coefficients.
    expected = {
        1: [1,1,2,5,18,75,410,2729,20906,181499,1763490,18943701,
            222822578,2847624899,39282739034,581701775369,9202313110506,
            154873904848803,2762800622799362,52071171437696453,
            1033855049655584786,21567640717569135515],
        2: [1,1,2,4,16,44,200,1288,9512,78652,744360,7867148,91310696,
            1154292796,15784573160,232050062524,3648471927912,
            61080818510972,1084657970877416,20361216987032284,
            402839381030339816,8377409956454452732]}
    exact = {}
    for theta in (1, 2):
        vals = [exact_distribution(n, theta=theta)[0] for n in range(22)]
        assert vals == expected[theta]
        exact[str(theta)] = vals
    results['OEIS_values'] = {'range': 'n=0..21, both sequences', 'matches': 44}
    (ROOT / 'data' / 'exact_values.json').write_text(json.dumps(exact, indent=2)+'\n')
    print('44 exact OEIS values: PASS', flush=True)

    parameters = [(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)]
    cases = moments_checked = 0
    for n in range(1, 9):
        brute = {(r,s,t): [0]*(n+1) for r,s in parameters for t in (1,2)}
        for p in permutations(range(n)):
            for r,s in parameters:
                positive = absolute = 0
                for i in range(max(0,n-r)):
                    delta = p[i+r] - p[i]
                    positive += delta == s
                    absolute += abs(delta) == s
                brute[r,s,1][positive] += 1
                brute[r,s,2][absolute] += 1
        for (r,s,t), distribution in brute.items():
            assert distribution == exact_distribution(n,r,s,t)
            cutoff = min(n//r,n//s,n//2)
            for k, moment in enumerate(stable_moments(n,r,s,t,cutoff)):
                numerator = sum(comb(j,k)*value for j,value in enumerate(distribution) if j>=k)
                assert moment == Fraction(numerator, factorial(n))
                moments_checked += 1
            cases += 1
    results['brute_force'] = {'n': '1..8', 'parameter_pairs': parameters,
                             'distribution_cases': cases,
                             'factorial_moment_equalities': moments_checked}
    print(f'{cases} brute distributions; {moments_checked} moments: PASS', flush=True)

    stabilization = 0
    for lengths in [(4,4),(4,5),(4,6),(5,5),(4,4,4),(4,5,6),(4,4,4,4)]:
        n, r = sum(lengths), len(lengths)
        for tiles, value in forest_tilings(lengths).items():
            k = n-len(tiles)
            if k > min(lengths):
                continue
            counter = Counter(a for a in tiles if a>1)
            b = tuple(counter.get(a,0) for a in range(2,max(counter,default=1)+1))
            assert stable_F(n,r,b) == value*profile_factorial(b)
            stabilization += 1
    results['unequal_path_stabilization'] = {'identities': stabilization}
    print(f'{stabilization} unequal-path identities: PASS', flush=True)

    degree_checks = 0
    for r,s in [(1,1),(1,3),(2,2),(2,3),(3,3)]:
        for d in range(7):
            for beta in defect_profiles(d):
                for j in range(7-d):
                    vals = [profile_coefficient(r,s,(m,)+beta,j) for m in range(2*j+5)]
                    for _ in range(2*j+1):
                        vals = [b-a for a,b in zip(vals, vals[1:])]
                    assert not any(vals)
                    degree_checks += 1
    results['polynomial_degree'] = {'extra_difference_checks': degree_checks}
    print(f'{degree_checks} polynomial-degree checks: PASS', flush=True)

    old = json.loads((ROOT/'data'/'coefficients_order16.json').read_text())
    arithmetic = 0
    for theta in (1,2):
        polynomials = correction_polynomials(16, theta=theta)
        assert [[str(a) for a in b] for b in polynomials] == old[str(theta)]['B']
        assert [str(a) for a in avoidance_coefficients(polynomials)] == old[str(theta)]['c']
        for J, poly in enumerate(polynomials):
            assert len(poly) <= 2*J+1
            if J:
                assert poly[0] == 0
            for a in poly:
                assert (a*factorial(2*J)).denominator == 1
                arithmetic += 1
    results['coefficient_regression'] = {'order': 16, 'integer_denominator_checks': arithmetic}
    results['status'] = 'All assertions passed. Finite checks only; see article for proofs.'
    (ROOT/'data'/'validation.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2), flush=True)


if __name__ == '__main__':
    main()
