#!/usr/bin/env python3
"""Exact direct enumeration: test only finite obstructions, not asymptotic claims."""
from collections import Counter
from fractions import Fraction
import json
import sympy as S
z = S.symbols('z')
states = [((), 0, ())]
expected = [1,1,2,4,10,27,83,277,1015,4007,17047]
rows=[]
for n in range(1,11):
    children=[]
    for word, asc, counts in states:
        for x in range(1 if not word else asc+2):
            if x < len(counts) and counts[x] == 2:
                continue
            newcounts=list(counts)+[0]*max(0,x+1-len(counts))
            newcounts[x]+=1
            children.append((word+(x,),asc+int(bool(word) and word[-1]<x),tuple(newcounts)))
    states=children
    assert len(states)==expected[n]
    asc_coeff=Counter(a for w,a,c in states)
    rep_coeff=Counter(sum(v==2 for v in c) for w,a,c in states)
    p=S.Poly(sum(v*z**k for k,v in asc_coeff.items()),z)
    r=S.Poly(sum(v*z**k for k,v in rep_coeff.items()),z)
    ps=p.sqf_part();rs=r.sqf_part()
    rows.append(dict(n=n,total=len(states),asc_coefficients=[int(p.nth(k)) for k in range(p.degree()+1)],rep_coefficients=[int(r.nth(k)) for k in range(r.degree()+1)],asc_all_real=bool(ps.count_roots(-S.oo,S.oo)==ps.degree()),rep_all_real=bool(rs.count_roots(-S.oo,S.oo)==rs.degree())))
    if n==7:
        assert r.as_expr()==1+21*z+126*z*z+129*z**3
        assert S.discriminant(r.as_expr(),z)==-84159
minor=S.Matrix([[1,1,S.Rational(2,3)],[1,1,1],[0,1,1]]).det()
assert minor==-S.Rational(1,3)
assert tuple(min(x,y) for x,y in zip((0,0,1),(0,1,0)))==(0,0,0)
print(json.dumps({'rows':rows,'n7_rep_discriminant':-84159,'normalized_toeplitz_minor':str(minor),'notes':'Finite checks only. No eventual regularity or asymptotic theorem follows.'},indent=2))
