#!/usr/bin/env python3
"""Exact finite certificates for the ordered-jet normal forms.

Uses integer quasi-shuffle expansions and rational/symbolic arithmetic.
This checks finite instances and displayed formulas, not analytic convergence.
"""
from __future__ import annotations
from collections import defaultdict
from functools import lru_cache
from itertools import permutations
from math import factorial, comb
from pathlib import Path
import json
import sympy as sp

@lru_cache(None)
def stuffle(a: tuple, b: tuple) -> dict:
    if not a: return {b: 1}
    if not b: return {a: 1}
    out = defaultdict(int)
    for w, c in stuffle(a[1:], b).items(): out[(a[0],) + w] += c
    for w, c in stuffle(a, b[1:]).items(): out[(b[0],) + w] += c
    merged = (a[0][0] + b[0][0], a[0][1] + b[0][1])
    for w, c in stuffle(a[1:], b[1:]).items(): out[(merged,) + w] += c
    return dict(out)

def product_words(words):
    out = {(): 1}
    for word in words:
        nxt = defaultdict(int)
        for old, coefficient in out.items():
            for new, c in stuffle(old, word).items(): nxt[new] += coefficient * c
        out = dict(nxt)
    return out

def set_partitions(items):
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for partition in set_partitions(rest):
        yield ((first,),) + partition
        for i in range(len(partition)):
            yield partition[:i] + ((first,) + partition[i],) + partition[i+1:]

def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in compositions(total - first, length - 1): yield (first,) + tail

def symmetric_certificate(ms):
    j = len(ms)
    lhs = defaultdict(int)
    for permutation in permutations(range(j)):
        lhs[tuple((1, ms[i]) for i in permutation)] += 1
    rhs = defaultdict(int)
    for partition in set_partitions(tuple(range(j))):
        coefficient = (-1) ** (j - len(partition))
        letters = []
        for block in partition:
            coefficient *= factorial(len(block) - 1)
            letters.append(((len(block), sum(ms[i] for i in block)),))
        for word, c in product_words(letters).items(): rhs[word] += coefficient * c
    assert {w:c for w,c in lhs.items() if c} == {w:c for w,c in rhs.items() if c}, ms

def main():
    count = 0
    for j in range(1, 6):
        for r in range(0, 5 if j < 5 else 3):
            for ms in compositions(r, j):
                symmetric_certificate(ms)
                count += 1
    contacts = 0
    for p in range(9):
        for q in range(9):
            n = p + q + 1
            lhs = -sp.Rational(factorial(p) * factorial(q), factorial(n)) * (comb(n,p+1)-comb(n,q+1))
            rhs = sp.Rational(1,q+1)-sp.Rational(1,p+1)
            assert lhs == rhs
            contacts += 1
    ranks = []
    for d in range(1,13):
        rank, orbit_count, word_count = 0,0,0
        for j in range(1,d+1):
            words=list(compositions(d-j,j))
            orbits={tuple(sorted(w)) for w in words}
            word_count += len(words); orbit_count += len(orbits)
            rank += len(words)-len(orbits)
        assert word_count == 2**(d-1)
        assert orbit_count == sp.partition(d)
        ranks.append(dict(depth=d,words=word_count,symmetric_orbits=orbit_count,orientation_rank=rank))
    X,Y,Q,P=(1,0),(1,1),(2,0),(2,1)
    assert stuffle((Y,),(X,X)) == {(Y,X,X):1,(X,Y,X):1,(X,X,Y):1,(P,X):1,(X,P):1}
    assert stuffle((X,),(Y,X)) == {(X,Y,X):1,(Y,X,X):2,(P,X):1,(Y,Q):1}
    assert stuffle((X,),(X,Y)) == {(X,X,Y):2,(X,Y,X):1,(Q,Y):1,(X,P):1}
    rays=[(1,1,1,2),(1,1,2,3),(1,2,3,4)]
    matrix=sp.Matrix([[-sp.Rational(b-d,2*a),-sp.Rational(b-2*c+d,6*a),sp.Rational(d*d-c*c,4*a*(a+b))] for a,b,c,d in rays])
    assert matrix.det() == -sp.Rational(1,144)
    expected_inverse=sp.Matrix([[0,-14,15],[-6,12,-9],[0,24,-24]])
    assert matrix.inv() == expected_inverse
    # Independently extract the constant term of the diagonal Newton formula.
    e,x,y,g2,g3,z,zp,zpp,z3,z3p,z4=sp.symbols('e x y g2 g3 z zp zpp z3 z3p z4')
    one=1/e+x-y*e+g2*e**2/2-g3*e**3/6
    two=z+2*zp*e+2*zpp*e**2
    three=z3+3*z3p*e
    newton=sp.expand((one**4-6*one**2*two+3*two**2+8*one*three-6*z4)/24).coeff(e,0)
    C4=(x**4-6*x*x*z+3*z*z+8*x*z3-6*z4)/24
    T=y*(x*x-z)/2+x*zp-z3p
    diagonal=C4-T+(x*g2+y*y-2*zpp)/4-g3/36
    assert sp.expand(newton-diagonal)==0
    A,B,C,cs2,cs3,cs4=sp.symbols('A B C c2 c3 c4')
    T0,D0,theta=A+B+C,A-C,A-2*B+C
    normal=(cs2+cs3+cs4)*T0/3+(cs2-cs4)*D0/2+(cs2-2*cs3+cs4)*theta/6
    assert sp.expand(normal-(cs2*A+cs3*B+cs4*C))==0
    gamma_bridge_count = 0
    for q in range(1,9):
        Yq=(1,q);Pprev=(2,q-1);Qprev=(3,q-1)
        residual=defaultdict(int)
        for word,coefficient in [((X,Yq),1),((Yq,X),-1)]:
            for i,(k,m) in enumerate(word):
                residual[word[:i]+((k+1,m),)+word[i+1:]] += -k*coefficient
                if m: residual[word[:i]+((k+1,m-1),)+word[i+1:]] += m*coefficient
            for new,c in stuffle((X,),word).items():residual[new] += coefficient*c
        for word,c in stuffle((X,),(Pprev,)).items():residual[word] -= q*c
        residual[(Qprev,)] += q
        residual[(Pprev,X)] += 2*q
        residual[(Yq,X,X)] += 2
        residual[(X,X,Yq)] -= 2
        assert not {word:c for word,c in residual.items() if c}, q
        gamma_bridge_count += 1
    report={
        'status':'PASS',
        'all_index_Gamma_bridge_word_certificates':gamma_bridge_count,
        'symmetric_sum_integer_certificates':count,
        'rational_contact_coefficient_checks':contacts,
        'rank_table':ranks,
        'three_explicit_quartic_stuffle_rows':'PASS',
        'quartic_linear_normal_form':'PASS',
        'independent_diagonal_Newton_constant_term':'PASS',
        'positive_rays':rays,
        'orientation_matrix':[[str(t) for t in row] for row in matrix.tolist()],
        'determinant':str(matrix.det()),
        'inverse':expected_inverse.tolist(),
        'scope':'Exact finite arithmetic. Analytic theorems are proved in the article; numerical period independence is not asserted.'
    }
    report['inverse']=[[int(t) for t in row] for row in report['inverse']]
    output=Path(__file__).resolve().parents[1]/'data'/'exact_checks.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
