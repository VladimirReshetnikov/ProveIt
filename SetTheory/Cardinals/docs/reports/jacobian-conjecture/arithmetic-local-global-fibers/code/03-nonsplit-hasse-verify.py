"""Replay finite certificates and exact symbolic identities.
Run from the package root: python code/verify.py
"""
from __future__ import annotations
import json
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from arithmetic import (keller, dyadic_condition, odd_obstruction, h_value,
                        reconstruct, exact_counts, integral_targets)


def main():
    checks = {}
    hist = Counter(tuple(v % 8 for v in keller(*point))
                   for point in product(range(8), repeat=3))
    for A, B, C in product(range(8), repeat=3):
        assert ((A, B, C) in hist) == dyadic_condition(A, B, C)
    checks['dyadic'] = {'targets_checked': 512, 'image_size': len(hist),
                        'fiber_histogram': dict(Counter(hist.get(t, 0)
                              for t in product(range(8), repeat=3)))}
    odd = []
    for p in (3,5,7,11,13,17,19,23,29,31):
        image = {tuple(v % p for v in keller(*point))
                 for point in product(range(p), repeat=3)}
        for A,B,C in product(range(p), repeat=3):
            rooted = any(h_value(s,A,B,C) % p == 0 for s in range(p))
            triple = (3*B*C-4) % p == 0 and (27*A*C*C-4) % p == 0
            assert ((A,B,C) in image) == (C == 0 or (rooted and not triple))
        odd.append({'prime':p, 'targets_checked':p**3, 'image_size':len(image)})
    checks['odd_prime_images'] = odd
    checks['odd_prime_total_targets'] = sum(row['targets_checked'] for row in odd)
    n = 0
    for x,y,z in product(range(-5,6), repeat=3):
        A,B,C = keller(x,y,z)
        assert dyadic_condition(A,B,C) and odd_obstruction(A,B,C) == 1
        if x and C:
            s = C*y + C//x
            assert C % x == 0 and h_value(s,A,B,C) == 0
            assert reconstruct(s,A,B,C) == (x,y,z)
        n += 1
    checks['integral_image_and_inverse_checks'] = n
    # Exhaustive small boxes: independently enumerate roots and integer fibers.
    small = []
    for T in (5,10,25,50):
        targets, split, nonsplit, integral = set(), set(), set(), set()
        R = isqrt(2*T)+3
        for A,B in product(range(-T,T+1), repeat=2):
            if B % 2:
                continue
            b = B//2
            roots = [r for r in range(-R,R+1) if r**3-r*r+b*r-A == 0]
            if not roots or not dyadic_condition(A,B,2) or odd_obstruction(A,B,2) != 1:
                continue
            targets.add((A,B))
            simple = [r for r in roots if 3*r*r-2*r+b != 0]
            for r in roots:
                assert gcd(3*r-1,3*b-1) == 1
            if len(roots) == 3:
                split.add((A,B))
            elif len(roots) == 1:
                nonsplit.add((A,B))
            for r in simple:
                d = 3*r*r-2*r+b
                point = (Fraction(1,d), r-d, 5*d*d-3*r*d-2*d**3)
                assert keller(*point) == (A,B,2)
                if abs(d) == 1:
                    integral.add((A,B))
        counts = exact_counts(T)
        assert len(targets) == counts['locally_soluble_targets']
        assert len(split) == counts['split_hasse']
        assert integral == integral_targets(T)
        assert len(nonsplit-integral) == counts['nonsplit_hasse']
        assert len(targets-integral) == counts['all_hasse']
        small.append(counts)
    checks['independent_small_boxes'] = small
    # Explicit rational-plus-irreducible-quadratic family.
    for b in range(2,102):
        point = (Fraction(1,b), -b, 5*b*b-2*b**3)
        assert keller(*point) == (0,2*b,2)
        assert 1-4*b < 0 and odd_obstruction(0,2*b,2) == 1
        assert dyadic_condition(0,2*b,2)
    checks['nonsplit_family_instances'] = 100
    checks['status'] = 'PASS'
    out = Path(__file__).resolve().parents[1]/'data'/'verification.json'
    out.write_text(json.dumps(checks, indent=2)+'\n')
    print(json.dumps(checks, indent=2))

if __name__ == '__main__':
    main()
