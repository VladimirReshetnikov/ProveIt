#!/usr/bin/env python3
"""Construct a colour-count partition for the general finite packing theorem.

The group is indexed 0..d-1, with identity 0. `add` is its addition.
Input counts are already translated to a baseline of colour 0.
Output table has reserve row 0 and one row per corrected target.
Only quotient witnesses are constructed, not the full residue representatives.
"""
from verify import patterns, plus, fixed_quota_oracle
from random import Random


def allocate(add, counts, quotas, targets):
    d = len(counts); r = len(targets)
    assert len(quotas) == r+1 and sum(counts) == sum(quotas)
    orders = [1]*d
    for a in range(1,d):
        x=a
        while x:
            x=add(x,a); orders[a]+=1
            assert orders[a]<=d
    assert all(n>=d-1 for n in quotas[1:])
    assert quotas[0]>=sum(o-1 for o in orders[1:])
    assert counts[0]>=(d-1)*(r+1)
    P=patterns(add,d)
    cap=tuple(min(x,(d-1)*r) for x in counts[1:])
    zero=(0,)*(d-1)
    layers=[{zero:None}]
    for t in targets:
        layer={}
        for prev in layers[-1]:
            for p in sorted(P[t]) if t else (zero,):
                nxt=tuple(a+b for a,b in zip(prev,p))
                if all(a<=b for a,b in zip(nxt,cap)):
                    layer.setdefault(nxt,(prev,p))
        if not layer: return None
        layers.append(layer)
    current=next(iter(layers[-1])); table=[[0]*d for _ in quotas]
    for j in range(r,0,-1):
        current,p=layers[j][current]
        table[j][1:]=p
    remaining=[counts[a]-sum(row[a] for row in table) for a in range(d)]
    room=[n-sum(row) for n,row in zip(quotas,table)]
    for a in range(1,d):
        rest=remaining[a]%orders[a]
        table[0][a]+=rest; room[0]-=rest; remaining[a]-=rest
    for a in range(1,d):
        while remaining[a]:
            n=orders[a]
            j=next(j for j,x in enumerate(room) if x>=n)
            table[j][a]+=n; room[j]-=n; remaining[a]-=n
    for j,x in enumerate(room): table[j][0]=x
    assert sum(room)==counts[0]
    return table


def validate(add,counts,quotas,targets,table):
    assert [sum(row) for row in table]==list(quotas)
    assert [sum(row[a] for row in table) for a in range(len(counts))]==list(counts)
    for row,t in zip(table[1:],targets):
        z=0
        for a,n in enumerate(row):
            for _ in range(n): z=add(z,a)
        assert z==t


def main():
    from itertools import product
    rng=Random(20261127); tests=0
    for kind in ['C4','V4']:
        add=lambda a,b: plus(kind,a,b)
        for _ in range(40):
            r=rng.randint(1,3)
            counts=(9+3*r,)+tuple(rng.randrange(7) for _ in range(3))
            quotas=[3]*r; quotas=[sum(counts)-sum(quotas)]+quotas
            oracle=fixed_quota_oracle(kind,counts,quotas[1:])
            for targets in product(range(4),repeat=r):
                table=allocate(add,counts,quotas,targets)
                assert (table is not None)==(targets in oracle)
                if table is not None: validate(add,counts,quotas,targets,table)
                tests+=1
    print(f'Constructive packing: {tests:,} comparisons against fixed-quota oracle passed.')

if __name__=='__main__': main()
