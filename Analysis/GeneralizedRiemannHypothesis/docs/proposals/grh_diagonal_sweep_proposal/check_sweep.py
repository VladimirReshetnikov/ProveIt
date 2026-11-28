#!/usr/bin/env python3
"""Finite regressions for the deterministic grid sweep; no Lean or third-party dependencies."""
from itertools import product
from math import prod
from fractions import Fraction


def end(m, word):
    return word.count('R'), m-word.count('D')


def word_at(m,j,b):
    # During stage j, after moving the new R past b-j-1 down steps.
    return 'R'*j+'D'*(m-b)+'R'+'D'*(b-j-1)


def sweep(m):
    halves=['D'*m]*2
    turns=[]
    for j in range(m):
        assert halves==['R'*j+'D'*(m-j)]*2
        assert all(end(m,w)==(j,j) and w[-1]=='D' for w in halves)
        halves=[w[:-1]+'R' for w in halves]
        turns.append((j,j))
        for z in (0,1):
            for b in range(j+1,m):
                before=halves[z]
                assert before==word_at(m,j,b)
                k=j+(m-b)-1
                assert before[k:k+2]=='DR'
                assert end(m,before[:k])==(j,b+1)
                halves[z]=before[:k]+'RD'+before[k+2:]
                assert halves[z]==word_at(m,j,b+1)
                assert all(end(m,w)==(j+1,j+1) for w in halves)
                turns.append((b,j) if z else (j,b))
        assert halves==['R'*(j+1)+'D'*(m-j-1)]*2
    assert halves==['R'*m]*2
    assert len(turns)==len(set(turns))==m*m
    assert set(turns)==set(product(range(m),repeat=2))
    assert sum(i==j for i,j in turns)==m
    return turns


def exponents(m,r,t,R):
    # Rank formula from New.Data.card_gridIndex, for z=0,1.
    rank=lambda z,i,j:r+z+i*(t+z)+j*(t-z)
    assert all(0<=rank(z,i,j)<=R for z in (0,1) for i in range(m+1) for j in range(m+1))
    A=sum(rank(z,0,j)**2 for z in (0,1) for j in range(m))
    E=sum(rank(0,j+1,j) for j in range(m))
    B=sum(rank(z,j,m)*rank(z,j+1,m) for z in (0,1) for j in range(m))
    assert E==m*r+t*m*m
    assert A<=2*m*R*R and B<=2*m*R*R and E<=m*R
    old=m*m*R+4*m*R*R
    uniform=m*R+4*m*R*R
    exact=A+E+B
    assert exact<=uniform<=old
    return A,E,B,old,uniform,exact


def main():
    for m in range(65):
        turns=sweep(m)
        # Test composition of nonzero scalar factors, order independent.
        scalar=lambda ij:Fraction(ij[0]+ij[1]+1,ij[0]+2*ij[1]+2)
        assert prod(map(scalar,turns))==prod(map(scalar,product(range(m),repeat=2)))
    print('Sweep: m=0..64; endpoint, corner orientation, mirror indices, exact square cover, scalar product: PASS')
    cases=0
    for m in range(0,21):
        for r in range(1,7):
            for t in range(1,9):
                R=2*(r+m*t+1)
                exponents(m,r,t,R)
                cases+=1
    print(f'Rank accounting: {cases} integer parameter sets; exact diagonal sum and all bound inequalities: PASS')
    # Tiny explicit matrix cardinality checks over arbitrary finite sets.
    for h in (1,2,3):
        for a,b in product(range(3),repeat=2):
            assert sum(1 for _ in product(range(h),repeat=a*b))==h**(a*b)
    print('Finite matrix cardinality: 27 explicit checks including empty matrices: PASS')
    m,r,t=10,9,45
    R=2*(r+m*t+1)
    A,E,B,old,uniform,exact=exponents(m,r,t,R)
    print(f'Illustrative (not asserted admissible) ranks: m={m}, r={r}, t={t}, R={R}')
    print(f'A={A}; E={E}; B={B}; old={old}; diagonal-only uniform={uniform}; endpoint-sensitive={exact}')
    print(f'Endpoint-sensitive / old exponent = {float(Fraction(exact,old)):.6f}')
    print('All checks passed. These are finite regressions, not a formal proof of the theta-lift theorems.')

if __name__=='__main__':
    main()
