#!/usr/bin/env python3
"""Enumerate the bilinear group {Q in GL_n(F_2): Q^T Q=I} for n<=6.

Checks every principal submatrix, using bitmask Gaussian elimination.
This checks small finite cases and the exact group/model distinction;
it is not evidence replacing the asymptotic proof.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json


def rank_bits(columns):
    pivots = {}
    for v in columns:
        while v:
            p = v.bit_length()-1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def orthogonal_columns(n):
    unit = [v for v in range(1, 1 << n) if v.bit_count() % 2]
    def extend(columns, candidates):
        if len(columns) == n:
            yield tuple(columns)
            return
        for v in candidates:
            remaining = [w for w in candidates if not ((v & w).bit_count() % 2)]
            yield from extend(columns+[v],remaining)
    yield from extend([],unit)


def expected_group_order(n):
    # O(2k+1,2) = Sp(2k,2); O(2k,2) has order 2^(2k-1)|Sp(2k-2,2)|.
    k = (n-1)//2
    sp = 2**(k*k)
    for j in range(1,k+1):
        sp *= 2**(2*j)-1
    return sp if n % 2 else 2**(n-1)*sp


def main():
    results = []
    for n in range(1,7):
        hist, count = Counter(), 0
        fixed = {mask:Counter() for mask in range(1<<n)}
        full = (1<<n)-1
        for cols in orthogonal_columns(n):
            count += 1
            # Orthogonality and fixed all-ones vector are direct invariants.
            assert all(((cols[i]&cols[j]).bit_count()&1) == (i == j)
                       for i in range(n) for j in range(n))
            total = 0
            for c in cols:
                total ^= c
            assert total == full
            maximum = 0
            for mask in range(1<<n):
                size = mask.bit_count()
                r = rank_bits([cols[j]&mask for j in range(n) if mask & (1<<j)])
                nullity = size-r
                assert nullity <= min(size,n-size)
                fixed[mask][nullity] += 1
                maximum = max(maximum,nullity)
            hist[maximum] += 1
        assert count == expected_group_order(n)
        # All coordinate sets of the same size have the same nullity law.
        laws = {}
        for mask, law in fixed.items():
            size = mask.bit_count()
            if size in laws:
                assert laws[size] == law
            else:
                laws[size] = law
        tails = {}
        for r in range(1,n//2+1):
            prob = Fraction(sum(v for k,v in hist.items() if k>=r),count)
            cert = Fraction(6)*Fraction(2)**(n-r*(r-1)//2)
            assert prob <= cert
            tails[r] = str(prob)
        results.append({'n':n,'group_order':count,
                        'maximum_principal_nullity_counts':dict(sorted(hist.items())),
                        'maximum_principal_nullity_tail_probabilities':tails,
                        'fixed_subset_nullity_counts_by_subset_size':{
                            size:dict(sorted(law.items())) for size,law in sorted(laws.items())}})
    data = {'status':'all exact checks passed',
            'scope':'Exhaustive n<=6 only; small-n asymptotic bound is usually vacuous.',
            'results':results}
    target = Path(__file__).resolve().parents[1] / 'checks' / 'binary_independent_checks.json'
    target.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'status':data['status'],
                      'results':[{k:x[k] for k in ['n','group_order','maximum_principal_nullity_counts']}
                                 for x in results]},indent=2))


if __name__ == '__main__':
    main()
