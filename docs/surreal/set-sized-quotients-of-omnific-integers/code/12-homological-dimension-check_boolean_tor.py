#!/usr/bin/env python3
"""Finite, exact regression tests for the Boolean Tor calculation.

This audits finitely many multidegrees after replacing (D,K) by
(Q,Q(sqrt(2))). It is not a proof for all rational exponents or for Z.
Requires Python 3.10+ and SymPy. No network access is used.
"""
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import sympy as sp


def subsets(items, size):
    return list(combinations(items, size))


def homology_at(alpha):
    """Build the graded flat-resolution tensor complex directly."""
    d = len(alpha)
    support = tuple(i for i, a in enumerate(alpha) if a > 0)
    terms = [[] for _ in range(d+1)]
    # C_0=(A/J)_alpha: rational coefficient =0, sqrt(2) coefficient =1.
    if not support:
        terms[0] = [((), 0)]
    else:
        generators = [j for j in range(d) if alpha[j] >= 1]
        if not generators:
            terms[0] = [((), 0), ((), 1)]
        elif len(support) == 1 and alpha[support[0]] == 1:
            terms[0] = [((), 1)]
        # In all remaining degrees J_alpha=K or A_alpha=0.
    for p in range(1,d+1):
        for S in subsets(support,p):
            # (J I_S)_alpha is K iff alpha-e_j belongs to I_S.
            killed = False
            for j in range(d):
                shifted = tuple(a-(1 if i==j else 0) for i,a in enumerate(alpha))
                if all(a>=0 for a in shifted) and all(shifted[i]>0 for i in S):
                    killed=True
                    break
            if not killed:
                terms[p].extend([(S,0),(S,1)])
    maps = [None]
    for p in range(1,d+1):
        targets = {item:i for i,item in enumerate(terms[p-1])}
        mat = sp.zeros(len(terms[p-1]),len(terms[p]))
        for col,(S,c) in enumerate(terms[p]):
            for r in range(len(S)):
                target=(S[:r]+S[r+1:],c)
                if target in targets:
                    mat[targets[target],col]+=(-1)**r
        maps.append(mat)
    for p in range(2,d+1):
        assert maps[p-1]*maps[p] == sp.zeros(len(terms[p-2]),len(terms[p]))
    ranks=[0]+[int(m.rank()) for m in maps[1:]]+[0]
    return [len(terms[p])-ranks[p]-ranks[p+1] for p in range(d+1)]


def predicted(alpha):
    d=len(alpha)
    expected=[0]*(d+1)
    if all(a==0 for a in alpha):
        expected[0]=1
    elif all(a in (0,1) for a in alpha):
        r=sum(a==1 for a in alpha)
        expected[r]=1 if r==1 else 2
    return expected


def main():
    grid=[Fraction(0),Fraction(1,3),Fraction(1,2),Fraction(1),Fraction(3,2)]
    counts={}
    for d in range(1,5):
        count=0
        for alpha in product(grid,repeat=d):
            actual=homology_at(alpha)
            expected=predicted(alpha)
            assert actual==expected,(alpha,actual,expected)
            count+=1
        counts[str(d)]=count
    report={"status":"PASS","coefficient_test_pair":"Q subset Q(sqrt(2))",
            "grid":[str(x) for x in grid],"grades_checked_by_rank":counts,
            "total_grades_checked":sum(counts.values()),
            "scope":"finite exact regression checks; not proof-assistant verification"}
    print(json.dumps(report,indent=2))
    Path(__file__).with_name('audit_results.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    main()
