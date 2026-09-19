#!/usr/bin/env python3
"""Independent exact checker. Does not import the generator or graph solver."""
import json
from math import isqrt, lcm
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def primes(n):
    return [p for p in range(2,n+1) if all(p % d for d in range(2,isqrt(p)+1))]


def factorial_v(n,p):
    total = 0
    while n:
        n //= p
        total += n
    return total


def integer_v(n,p):
    require(n != 0, 'Zero denominator')
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def check_one(c):
    top, bot, ks, p = c['numerator'], c['denominator'], c['slopes'], c['prime']
    require(sum(top)==sum(bot) and len(bot)==len(top)+1, 'Ratio assumptions')
    require(p in primes(p), 'Composite prime parameter')
    L = lcm(*(top+bot))
    require(L == c['grid'], 'Bad grid')
    delta = [sum(a*j//L for a in top)-sum(b*j//L for b in bot) for j in range(L)]
    require(all(t in (0,1) for t in delta), 'Landau positivity')
    # Large primes are handled by the proved cutoff theorem, not sampling.
    require(len(ks)==len(set(ks)), 'Repeated root')
    for k in ks:
        require(sum(a%k==0 for a in top)-sum(b%k==0 for b in bot)==-1, 'Bad slope')
    states = [tuple(s) for s in c['states']]
    h = c['potential']
    require(len(states)==len(set(states))==len(h), 'Duplicated/missing states')
    require(all(type(value) is int for value in h), 'Noninteger potential')
    require(all(all(t is None or type(t) is int for t in state) for state in states),
            'Noninteger state coordinate')
    index = {s:i for i,s in enumerate(states)}
    initial, terminal = (0,)+(1,)*len(ks), (0,)+(None,)*len(ks)
    require(states[0] == initial and terminal in index, 'Missing endpoints')
    require(h[index[terminal]]==0 and h[0]==c['minimum'], 'Endpoint potentials')
    count = 0
    for i,s in enumerate(states):
        require(0 <= s[0] < L and len(s)==len(ks)+1, 'State dimensions')
        for k,t in zip(ks,s[1:]):
            require(t is None or 1 <= t <= k, 'Carry outside finite range')
        for digit in range(p):
            j = (s[0]+L*digit)//p
            out = [j]
            alive = 0
            for k,t in zip(ks,s[1:]):
                if t is None or (k*digit+t) % p:
                    out.append(None)
                else:
                    out.append((k*digit+t)//p)
                    alive += 1
            ns = tuple(out)
            require(ns in index, 'State set is not closed')
            require(h[i] <= delta[j]-alive+h[index[ns]], 'Potential inequality fails')
            count += 1
    require(count == c['edge_count'], 'Edge count mismatch')
    n = c['witness']
    require(n >= 0, 'Negative witness')
    actual = sum(factorial_v(a*n,p) for a in top)-sum(factorial_v(b*n,p) for b in bot)
    actual -= sum(integer_v(k*n+1,p) for k in ks)
    require(actual == h[0], 'Sharpness witness fails')
    return count


def main(path):
    document = json.loads(Path(path).read_text())
    count, states, edges = 0,0,0
    expected = {
        ((30,1),(15,10,6),(2,)):7,
        ((30,1),(15,10,6),(3,)):1,
        ((30,1),(15,10,6),(5,)):1,
        ((30,1),(15,10,6),(2,3,5)):42,
        ((12,1),(6,4,3),(1,)):385,
        ((12,1),(6,4,3),(2,)):5,
        ((12,1),(6,4,3),(3,)):1,
        ((12,1),(6,4,3),(1,2,3)):770,
    }
    seen=set()
    require(len(document['cases'])==len(expected), 'Missing or extra quotient cases')
    for case in document['cases']:
        key=tuple(tuple(case[field]) for field in ('numerator','denominator','slopes'))
        require(key in expected and key not in seen, 'Wrong or repeated quotient')
        require(case['optimal_multiplier']==expected[key], 'Claim differs from the article')
        seen.add(key)
        top,bot,ks = case['numerator'],case['denominator'],case['slopes']
        cutoff = max([max(top+bot)] + [abs(k-j) for k in ks for j in ks])
        require(case['cutoff']==cutoff, 'Invalid cutoff')
        cs=case['certificates']
        require([c['prime'] for c in cs]==primes(cutoff), 'Missing small-prime coverage')
        multiplier=1
        for c in cs:
            require(c['numerator']==top and c['denominator']==bot and c['slopes']==ks,
                    'Certificate is for wrong problem')
            edges += check_one(c)
            count += 1
            states += len(c['states'])
            multiplier *= c['prime']**max(0,-c['minimum'])
        require(multiplier==case['optimal_multiplier'], 'Incorrect optimal multiplier')
    print(f'PASS: {len(document["cases"])} cases; {count} prime certificates; '
          f'{states} states; {edges} exact transition inequalities.')
    print('All prime-coverage, potential, and sharpness checks passed.')


if __name__=='__main__':
    default=Path(__file__).resolve().parents[1]/'data'/'certificates.json'
    main(sys.argv[1] if len(sys.argv)>1 else default)
