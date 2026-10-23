#!/usr/bin/env python3
"""Construct and directly certify 32 four-sum-distinct digit positions.

No finite-field theorem is needed to trust the final collision check.
The finite-field construction is a reproducible source of the candidates.
"""
from itertools import combinations_with_replacement
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Run without -O: assertions are part of the certificate.')
DEGREE=20
POLY=(1<<20)|(1<<3)|1
ORDER=(1<<20)-1

def mul(a,b):
    out=0
    while b:
        if b&1: out^=a
        b>>=1
        a<<=1
        if a&(1<<DEGREE): a^=POLY
    return out

def power(a,n):
    out=1
    while n:
        if n&1: out=mul(out,a)
        a=mul(a,a); n>>=1
    return out

def construct():
    assert power(2,ORDER)==1
    assert all(power(2,ORDER//p)!=1 for p in (3,5,11,31,41))
    logs={}; v=1
    for i in range(ORDER):
        assert v not in logs
        logs[v]=i
        v<<=1
        if v&(1<<DEGREE): v^=POLY
    assert v==1 and len(logs)==ORDER
    eta=power(2,ORDER//31)
    field=[0]; a=1
    for _ in range(31):
        field.append(a); a=mul(a,eta)
    assert len(set(field))==32 and all(power(a,32)==a for a in field)
    raw=sorted(logs[2^a] for a in field)
    # Translation preserves B4 modulo ORDER. Put the largest circular gap
    # across the endpoint to minimize the largest ordinary nonnegative weight.
    gaps=[(raw[(i+1)%32]-raw[i])%ORDER for i in range(32)]
    cut=max(range(32),key=lambda i:gaps[i])
    shift=raw[(cut+1)%32]
    positions=sorted((v-shift)%ORDER for v in raw)
    assert positions[0]==0 and len(set(positions))==32
    seen={}; ordinary={}
    for indices in combinations_with_replacement(range(32),4):
        total=sum(positions[i] for i in indices)
        assert total%ORDER not in seen
        assert total not in ordinary
        seen[total%ORDER]=indices
        ordinary[total]=indices
    assert len(seen)==52360
    digest=hashlib.sha256(json.dumps(sorted((k,list(v)) for k,v in ordinary.items()),separators=(',',':')).encode()).hexdigest()
    return {'construction':'Bose-Chowla B4 in GF(32^4), followed by direct exhaustive four-multiset check',
        'field_polynomial_binary':POLY,'field_polynomial':'x^20+x^3+1',
        'generator_binary':2,'group_order':ORDER,'prime_divisors':[3,5,11,31,41],
        'subfield_generator_binary':eta,'raw_logarithms':raw,'translation':shift,
        'positions_including_zero':positions,'witness_positions':positions[1:],
        'max_position':positions[-1],'four_multisets':len(seen),
        'ordinary_sums_sha256':digest,'collision_check':'Exact exhaustive check, not randomized'}

if __name__=='__main__':
    data=construct()
    (ROOT/'B4_CERTIFICATE.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
