#!/usr/bin/env python3
"""Finite exact checks of the general bound and bubble fragment bookkeeping.

These are reproducible consistency tests, not an all-size proof, an exhaustive
NFA census, or proof-assistant certification. Standard library only.
"""
from fractions import Fraction
from itertools import product
from math import gcd
import json


def arithmetic(max_n=100):
    equal = unequal = core = 0
    for n in range(1, max_n + 1):
        if n >= 2:
            assert (n - 1) ** 2 + 4 <= n * n + 8 * n
        if 2 <= n <= 5:
            assert 2 * ((n - 1) ** 2 + 1) + 1 <= n * n + 8 * n
        for j in range(n // 2 + 1, n):
            for k in range(j + 1, n + 1):
                if gcd(j, k) != 1:
                    continue
                assert n + j * (k - 2) <= j * k
                for ell, r in ((j, k), (k, j)):
                    for m in range(ell, n + 1):
                        h = m - ell
                        d = Fraction(h, ell)
                        assert 0 <= d < 1
                        d0 = 2 * n + ell - 3
                        bound = j * k * (1 + d) + d0 + 2 * m + 1
                        assert bound == r * m + d0 + 2 * m + 1
                        assert bound <= n * n + 5 * n
                        assert d0 + (ell - 1) * (r - 1) == j*k + 2*n-r-2
                        equal += 1
                for m in range(k, n + 1):
                    mu = Fraction(m - j + 2, k)
                    assert j + k >= m + 2
                    assert 0 <= mu <= 1
                    assert (k-j)*(j+k-m-2) >= 0
                    bound = 2*mu*j*k + (2*n-2) + 2*(2-mu)*(m-1) + 3
                    assert bound <= 2*j*(m-j+2) + 6*n-3
                    assert bound <= n*n + 8*n
                    unequal += 1
        for c in range(1, n + 1):
            assert n-c+c*c+8*c <= n*n+8*n
            assert c*c+n-3*c+2 <= n*n
            for d in range(2, c + 1):
                f = Fraction((n-c)*d) + Fraction(2*c*c, d)
                assert f <= n*n
                bound = f + 4*d+2*n-3
                assert bound <= n*n+6*n-3
                m = c//d
                t = d*((m-1)**2+1)+2*d-2
                assert t <= Fraction(c*c, d)+2*d-2
                core += 1
    return {'maximum_states': max_n, 'equal_cycle_parameter_cases': equal,
            'unequal_cycle_parameter_cases': unequal,
            'imprimitive_parameter_cases': core, 'passed': True}


def make_bubbles(spec):
    """A circular chain; entry (a,b) is a bubble, integer is shared path.

    Our fixtures use shared paths as several successive common edges. Distinct
    bubble alternatives are monochromatic. A sole bubble has a return endpoint.
    """
    count = len(spec)
    rows = [[0]*count for _ in (0, 1)]
    charges = {}
    choices = []
    def vertex():
        q = len(rows[0])
        rows[0].append(0); rows[1].append(0)
        return q
    def edge(u, v, labels, charge):
        for label in labels:
            rows[label][u] |= 1 << v
        charges[u, v] = charge
    for i, lengths in enumerate(spec):
        target = (i+1) % count
        if isinstance(lengths, int):
            assert lengths == 1
            edge(i, target, (0,1), 0)
            choices.append(([i, target], [i, target]))
            continue
        paths = []
        for letter, length in enumerate(lengths):
            path = [i] + [vertex() for _ in range(length-1)] + [target]
            for index, (u,v) in enumerate(zip(path,path[1:])):
                charge = (int(index > 0) if lengths[0] == lengths[1]
                          else 1+int(index == 0))
                edge(u,v,(letter,),charge)
            paths.append(path)
        choices.append(tuple(paths))
    # A canonical block with a 0-cycle followed by a 1-cycle, based at common 0.
    walk = [0]
    for letter in (0, 1):
        for pair in choices:
            walk += pair[letter][1:]
    assert walk[0] == walk[-1] == 0
    return rows, charges, walk


def image(mask, rows):
    result = 0
    while mask:
        low = mask & -mask
        mask -= low
        result |= rows[low.bit_length()-1]
    return result


def bubble_checks():
    fixtures = [((3,3),), ((2,2),1,(2,2)), ((2,3),),
                ((2,3),1,(2,2)), ((3,3),(2,4))]
    results=[]
    count=0
    for spec in fixtures:
        rows, charges, walk = make_bubbles(spec)
        q=len(rows[0]); length=len(walk)-1
        edges=[rows[0][u] | rows[1][u] for u in range(q)]
        rev=[sum(1<<u for u in range(q) if edges[u] & (1<<v)) for v in range(q)]
        prefix=[1]; suffix=[1]
        for _ in range(length):
            prefix.append(image(prefix[-1],edges))
            suffix.append(image(suffix[-1],rev))
        checks=0
        for start in range(length):
            for end in range(start+1, min(length,start+7)+1):
                charge=sum(charges[walk[i],walk[i+1]] for i in range(start,end))
                for target in product((0,1),repeat=end-start):
                    # A literal exact-length relation DP; singletons licensed.
                    dp=[0]+[length+1]*(end-start)
                    for i in range(end-start):
                        states=prefix[start+i]
                        for j in range(i+1,end-start+1):
                            states=image(states,rows[target[j-1]])
                            if j==i+1 or states & suffix[length-start-j]:
                                dp[j]=min(dp[j],dp[i]+1)
                    assert dp[-1] <= charge+1, (spec,start,end,target,dp,charge)
                    checks+=1
        count+=checks
        results.append({'chain': spec, 'states':q, 'ambient_walk_length':length,
                        'target_segment_checks':checks})
    return {'fixtures':results,'maximum_target_segment_length':7,
            'total_target_segment_checks':count,'passed':True}


def main():
    print(json.dumps({'scope':'Finite consistency checks only; mathematical proof is in the article',
                      'arithmetic':arithmetic(), 'bubble_fragments':bubble_checks(),
                      'all_checks_passed':True},indent=2))


if __name__=='__main__':
    main()
