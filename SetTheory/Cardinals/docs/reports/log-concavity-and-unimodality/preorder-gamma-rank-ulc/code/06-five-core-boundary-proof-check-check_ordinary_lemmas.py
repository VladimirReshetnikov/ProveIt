#!/usr/bin/env python3
"""Exact corroboration of the ordinary rank-four boundary proofs.

Uses only the Python standard library. It audits all local Boolean implications,
all head-monomial coefficient patterns for the sharpened core inequality, and
both elementary square completions. This is not a numerical positivity test.
"""
import itertools as it
import json
from fractions import Fraction as Q
from pathlib import Path

V=tuple(range(5))

def cover(S,J,arcs):
    return any(all((s,j) in arcs for s,j in zip(T,J)) for T in it.permutations(S,len(J)))


def audit_local_pair():
    A=set(range(4)); h=4;i=0;j=1
    edges=[(s,t) for t in (h,i,j) for s in sorted(A) if s!=t]
    checked=0
    for mask in range(1<<len(edges)):
        arcs={e for k,e in enumerate(edges) if mask>>k&1}
        if not cover(A,[h],arcs):continue
        ai=cover(A-{i},[h],arcs);aj=cover(A-{j},[h],arcs)
        bi=cover(A-{i},[i],arcs);bj=cover(A-{j},[j],arcs)
        di=cover(A-{i},[h,i],arcs);dj=cover(A-{j},[h,j],arcs)
        a=cover(A-{i,j},[h],arcs)
        b=cover(A-{i,j},[i],arcs);c=cover(A-{i,j},[j],arcs)
        d=cover(A-{i,j},[h,i],arcs);e=cover(A-{i,j},[h,j],arcs)
        f=cover(A-{i,j},[i,j],arcs)
        assertions=[ai+aj>=1+a,ai*aj>=a,bi>=b,bj>=c,
                    di>=d,bi*aj>=d,di+bi*aj>=b,
                    dj>=e,bj*ai>=e,dj+bj*ai>=c,
                    bi*bj>=f,di*aj>=d,dj*ai>=e,di*bj+dj*bi>=f]
        assert all(assertions),(arcs,assertions)
        checked+=1
    return {'arc_bits':len(edges),'all_patterns':1<<len(edges),
            'nonempty_extra_head_patterns_checked':checked,'passed':True}


def termlist(k,r):
    out=[]
    for S in it.combinations(V,k):
        for J in it.combinations([v for v in V if v not in S],r):
            u=tuple(int(v in S) for v in V)
            h=tuple(int(v in J) for v in V)
            out.append((u,h,S,J))
    return out


def audit_core():
    T={(k,r):termlist(k,r) for k,r in [(3,2),(3,0),(3,1),(2,2),(4,0),(2,1),(4,1)]}
    expr=[(4,(3,2),(3,0)),(2,(3,1),(3,1)),(-1,(2,2),(4,0)),(-4,(2,1),(4,1))]
    results=[]
    for goal in [(2,0,0,0,0),(1,1,0,0,0)]:
        heads=[i for i,c in enumerate(goal) if c]
        edges=[(s,j) for j in heads for s in V if s!=j]
        coefficient_evaluations=0; global_min=None
        for mask in range(1<<len(edges)):
            arcs={e for k,e in enumerate(edges) if mask>>k&1}
            cache={}
            def ok(S,J):
                key=(S,J)
                if key not in cache:cache[key]=cover(S,J,arcs)
                return cache[key]
            coefficients={}
            for scale,left,right in expr:
                for u1,h1,S1,J1 in T[left]:
                    for u2,h2,S2,J2 in T[right]:
                        if tuple(a+b for a,b in zip(h1,h2))!=goal:continue
                        mon=tuple(a+b for a,b in zip(u1,u2))
                        coefficients[mon]=coefficients.get(mon,0)+scale*ok(S1,J1)*ok(S2,J2)
            assert coefficients
            assert min(coefficients.values())>=0,(goal,arcs,coefficients)
            coefficient_evaluations+=len(coefficients)
            minimum=min(coefficients.values())
            global_min=minimum if global_min is None else min(global_min,minimum)
        results.append({'head_exponents':goal,'arc_patterns':1<<len(edges),
                        'tail_monomials_per_pattern':len(coefficients),
                        'coefficient_evaluations':coefficient_evaluations,
                        'minimum_coefficient':global_min,'passed':True})
    return results


def square(linear):
    out={}
    for i,a in enumerate(linear):
        for j,b in enumerate(linear):
            m=tuple(int(k==i)+int(k==j) for k in range(len(linear)))
            out[m]=out.get(m,Q(0))+a*b
    return out


def audit_completions():
    # Finite-sink completion, ordered X,Y,Z.
    target={(2,0,0):Q(1),(0,2,0):Q(11,27),(0,0,2):Q(1,2),
            (1,1,0):Q(2,3),(1,0,1):Q(-2,3),(0,1,1):Q(-2,3)}
    rhs={}
    for weight,linear in [(Q(1),(Q(1),Q(1,3),Q(-1,3))),
                          (Q(8,27),(Q(0),Q(1),Q(-3,4))),
                          (Q(2,9),(Q(0),Q(0),Q(1)))]:
        for mon,c in square(linear).items():rhs[mon]=rhs.get(mon,Q(0))+weight*c
    assert all(rhs.get(k,0)==target.get(k,0) for k in set(rhs)|set(target))
    # Four-tail Cauchy completion, ordered y_0,...,y_3.
    lhs=square((Q(1),)*4)
    lhs={m:3*c for m,c in lhs.items()}
    for i,j in it.combinations(range(4),2):
        mon=tuple(int(k==i)+int(k==j) for k in range(4));lhs[mon]-=8
    rhs={}
    for i,j in it.combinations(range(4),2):
        lin=tuple(Q(int(k==i)-int(k==j)) for k in range(4))
        for mon,c in square(lin).items():rhs[mon]=rhs.get(mon,Q(0))+c
    assert all(rhs.get(k,0)==lhs.get(k,0) for k in set(rhs)|set(lhs))
    return {'finite_sink_three_square_identity':True,'four_tail_cauchy_identity':True}


if __name__=='__main__':
    receipt={'local_pair_implications':audit_local_pair(),
             'strengthened_core_inequality':audit_core(),
             'square_completions':audit_completions(),
             'scope':'Last actual-degree-four inequality only; ordinary proofs are the logical basis.'}
    print(json.dumps(receipt,indent=2))
    Path(__file__).with_name('verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
