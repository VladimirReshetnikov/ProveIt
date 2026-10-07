#!/usr/bin/env python3
"""Exact finite checks for Schur-defect and third-energy classifications.

Finite enumerations are independent checks, not proofs of the all-real results.
Only Python standard-library arithmetic is used.
"""
import argparse
from collections import Counter
from itertools import combinations
from math import gcd
import json
from pathlib import Path


def schur_defect(c, cutoff=None):
    seen = set()
    ans = 0
    for j, z in enumerate(c):
        ans += j - sum(z-x in seen for x in seen)
        if cutoff is not None and ans > cutoff:
            return ans
        seen.add(z)
    return ans


def energy_defect(a):
    m = len(a)
    r = Counter(x-y for x in a for y in a)
    return ((2*m**3+m)//3 - sum(v*v for v in r.values()))//4


def normalize(a):
    a = tuple(sorted(a))
    a = tuple(x-a[0] for x in a)
    d = 0
    for x in a:
        d = gcd(d,x)
    return tuple(x//d for x in a) if d else a


def reflected_class(a):
    a = normalize(a)
    return min(a, tuple(a[-1]-x for x in reversed(a)))


def partition_vectors(n, s, low=0):
    if n == 0:
        if s == 0:
            yield ()
        return
    for x in range(low, s//n+1):
        for rest in partition_vectors(n-1, s-x, x):
            yield (x,) + rest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('structural_checks.json'), help='JSON report path; defaults beside this verifier')
    args = parser.parse_args()
    report = {"integer_schur_tests": {}, "partition_models": {},
              "third_energy_tests": {}, "threshold_counterexample": {}}
    for n in range(5,10):
        found = set()
        count = 0
        for c in combinations(range(1,21), n):
            count += 1
            if schur_defect(c, 2) != 2:
                continue
            d = c[0]
            assert all(x % d == 0 for x in c), c
            found.add(tuple(x//d for x in c))
        expected = {tuple(range(1,n))+(n+2,),
                    tuple(range(1,n-1))+(n,n+1)}
        if n == 5:
            expected.add((1,2,4,5,6))
        assert found == expected, (n,found,expected)
        report["integer_schur_tests"][n] = {"sets_checked":count,
                                                   "normalized_models": sorted(found)}
    for s in range(1,9):
        n = 5*s-1
        models = []
        for lam in partition_vectors(n, s):
            c = tuple(j+x for j,x in enumerate(lam,1))
            assert schur_defect(c) == s, (s,c)
            models.append(c)
        report["partition_models"][s] = {"n":n,"count":len(models)}
    for m in range(6,10):
        found = set()
        checked = 0
        for b in combinations(range(1,21),m-1):
            a = (0,)+b
            checked += 1
            if energy_defect(a) == 2*m-6:
                found.add(reflected_class(a))
        j = tuple(x for x in range(m+1) if x != 2)
        k = (0,)+tuple(range(2,m))+(m+1,)
        expected = {reflected_class(j),reflected_class(k)}
        if m == 6:
            expected.add((0,1,2,4,5,6))
        assert found == expected, (m,found,expected)
        report["third_energy_tests"][m] = {"sets_checked":checked,
                                         "affine_reflection_classes":sorted(found)}
    a = (0,1,2,4,5,6)
    assert energy_defect(a) == 6
    report["threshold_counterexample"] = {"set":a,"energy_defect":6,
                       "energy":(2*6**3+6)//3-4*6,"third_energy":(2*6**3+6)//3-8*3}
    target = args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
