#!/usr/bin/env python3
"""Exact arithmetic checks for the general geometric-mask classification.

For q=M^(-1/d), compare prime-valuation divisibility with the canonical period,
then compare residue-prefix inequalities with a generic bipartite matching
algorithm. All q arithmetic is exact; no floating-point root is used.
"""
from itertools import product
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json


def valuations(n):
    exponents = []
    p = 2
    while p*p <= n:
        e = 0
        while n%p == 0:
            n //= p
            e += 1
        if e:
            exponents.append(e)
        p += 1
    if n>1:
        exponents.append(1)
    return exponents


def canonical_period(m,d):
    g = d
    for e in valuations(m):
        g = gcd(g,e)
    return d//g


def matching_covers(source,target,allowed):
    owner = {}
    def augment(j,seen):
        for i in source:
            if i in seen or not allowed(i,j):
                continue
            seen.add(i)
            if i not in owner or augment(owner[i],seen):
                owner[i] = j
                return True
        return False
    return all(augment(j,set()) for j in target)


def prefix_condition(source,target,period,n):
    for j in range(1,n+1):
        if sum(i<=j and (j-i)%period==0 for i in source) < sum(i<=j and (j-i)%period==0 for i in target):
            return False
    return True


def main():
    n = 6
    masks = [tuple(i+1 for i,bit in enumerate(bits) if bit) for bits in product((0,1),repeat=n)]
    configurations = pairs = dominant = power_checks = 0
    examples = []
    for m in range(2,13):
        for d in range(1,5):
            period = canonical_period(m,d)
            prime_powers = valuations(m)
            for k in range(1,31):
                exact = all((e*k)%d==0 for e in prime_powers)
                assert exact == (k%period==0)
                power_checks += 1
            def allowed(i,j):
                return i<=j and all((e*(j-i))%d==0 for e in prime_powers)
            for source in masks:
                for target in masks:
                    prefix = prefix_condition(source,target,period,n)
                    matching = matching_covers(source,target,allowed)
                    assert prefix == matching, (m,d,source,target)
                    pairs += 1
                    dominant += prefix
            examples.append(dict(integer=m,root_degree=d,least_period=period))
            configurations += 1
    rational_cases = 0
    for q in (F(2,3),F(3,5),F(4,7)):
        for k in range(1,31):
            assert (q.denominator**k)%(q.numerator**k) != 0
        def allowed(i,j):
            return i<=j and (q.denominator**(j-i))%(q.numerator**(j-i))==0
        for source in masks:
            for target in masks:
                assert matching_covers(source,target,allowed) == set(target).issubset(source)
                rational_cases += 1
    assert canonical_period(4,2)==1
    assert canonical_period(2,2)==2
    assert matching_covers((1,2),(2,3),lambda i,j:i<=j and (j-i)%2==0)
    result=dict(status='passed',arithmetic='integer prime valuations and rational powers',
                root_parameter_configurations=configurations,power_membership_checks=power_checks,
                residue_prefix_vs_matching_pairs=pairs,dominant_pairs=dominant,
                nonexceptional_rational_pairs=rational_cases,canonical_periods=examples,
                scope='Finite arithmetic regression. The countable-transform and universal-kernel statements are proved analytically.')
    Path(__file__).with_name('arithmetic_order_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('canonical_periods','scope')},sort_keys=True))


if __name__=='__main__':
    main()
