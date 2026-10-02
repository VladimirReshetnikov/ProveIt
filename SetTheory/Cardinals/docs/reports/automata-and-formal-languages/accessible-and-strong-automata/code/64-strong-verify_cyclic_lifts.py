"""Exhaustive, independent connected cyclic-voltage lift counts at small sizes."""
from itertools import product
from math import prod
from pathlib import Path
import json

def strong(n, k, arcs):
    reverse = [[] for _ in range(n)]
    for v in range(n):
        for target in arcs[k*v:k*(v+1)]:
            reverse[target].append(v)
    for adjacency in ([arcs[k*v:k*(v+1)] for v in range(n)], reverse):
        seen, todo = {0}, [0]
        while todo:
            for target in adjacency[todo.pop()]:
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        if len(seen) != n:
            return False
    return True

def jordan(rank, ell):
    primes, z, p = [], ell, 2
    while p*p <= z:
        if z % p == 0:
            primes.append(p)
            while z % p == 0:
                z //= p
        p += 1
    if z > 1:
        primes.append(z)
    value = ell**rank
    for p in primes:
        value = value // p**rank * (p**rank-1)
    return value

out = []
for k,m,ell in [(2,1,2),(2,1,3),(2,2,2),(2,2,3)]:
    expected = ell**(m-1)*jordan((k-1)*m+1,ell)
    quotients = 0
    for q in product(range(m), repeat=k*m):
        if not strong(m,k,q):
            continue
        quotients += 1
        connected = 0
        for voltage in product(range(ell), repeat=k*m):
            arcs = tuple(ell*q[k*v+a]+(z+voltage[k*v+a])%ell
                         for v in range(m) for z in range(ell) for a in range(k))
            connected += strong(m*ell,k,arcs)
        assert connected == expected, (k,m,ell,q,connected,expected)
    out.append({'k':k,'quotient_states':m,'cycle_length':ell,
                'strong_quotients':quotients,'voltage_assignments_per_quotient':ell**(k*m),
                'strong_lifts_per_quotient':expected,'passed':True})
Path(__file__).with_name('cyclic_lift_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed exhaustive connected cyclic-lift checks for all four parameter cases.')
