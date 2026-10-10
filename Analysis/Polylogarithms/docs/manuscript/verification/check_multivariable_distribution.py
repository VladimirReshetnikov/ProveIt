"""Independent binary ranks in the original point/monomial presentation.

No normal-form, Koszul or incoming implementation is imported. This checks
finite consequences of the multivariable theorem, not its universal proof.
"""
from pathlib import Path
from itertools import product
from math import prod
import json
B=Path(__file__).resolve().parents[1]
def primes(q):
    return [p for p in range(2,q+1) if q%p==0 and all(p%d for d in range(2,p))]
def phi(q):
    value=q
    for p in primes(q): value=value//p*(p-1)
    return value
def rank(rows):
    pivots={}
    for value in rows:
        while value:
            col=value.bit_length()-1
            if col in pivots: value^=pivots[col]
            else: pivots[col]=value; break
    return len(pivots)
def matrices(q,lengths,powers,unit_branches):
    active=[p for p in primes(q) if p>2 or q%4==0]
    assert len(active)==len(lengths)==len(powers)
    monomials=list(product(*(range(L) for L in lengths)))
    indices={m:i for i,m in enumerate(monomials)};width=len(monomials)
    weights={}
    for p in primes(q):
        if p not in active: weights[p]=[None]  # the inactive A2 is fixed at one
        else:
            j=active.index(p)
            # Odd weights are 1+t_j^d. At 2, use either root of A2(A2-1).
            weights[p]=[None,(j,powers[j])] if p>2 or unit_branches else [(j,powers[j])]
    rows=[]
    for p in primes(q):
        for k in range(q//p):
            roots=[k+j*(q//p) for j in range(p)];target=p*k
            for m in monomials:
                index=indices[m];row=0
                for x in roots: row^=1<<(x*width+index)
                for shift in weights[p]:
                    mm=list(m)
                    if shift is not None:
                        j,d=shift;mm[j]+=d
                        if mm[j]>=lengths[j]: continue
                    row^=1<<(target*width+indices[tuple(mm)])
                rows.append(row)
    reflected=rows[:]
    for x in range(q):
        for i in range(width):reflected.append((1<<(x*width+i))^(1<<(((-x)%q)*width+i)))
    return rows,reflected,q*width
checks=[]
for q in [3,4,6,8,9,12,15,20,24,30,60,105]:
    r=len([p for p in primes(q) if p>2 or q%4==0])
    shapes=sorted(set([(1,)*r,(2,)*r,tuple(2+(j%2) for j in range(r)),(3,)*r]))
    for lengths in shapes:
        exponents=sorted(set([(1,)*r,lengths,tuple(L+1 for L in lengths),
                              tuple(1 if j%2 else L for j,L in enumerate(lengths))]))
        for powers in exponents:
            for branch in ([False,True] if q%4==0 else [False]):
                a,b,total=matrices(q,lengths,powers,branch)
                unref=total-rank(a);reflected=total-rank(b)
                expected_unref=phi(q)*prod(lengths)
                expected=phi(q)//2*prod(lengths)+2**(r-1)*prod(min(d,L) for d,L in zip(powers,lengths))
                assert unref==expected_unref and reflected==expected,(q,lengths,powers,branch,unref,reflected,expected)
                checks.append(dict(q=q,lengths=lengths,powers=powers,two_root_one=branch,
                                   columns=total,unreflected_dimension=unref,
                                   reflected_dimension=reflected,expected=expected,passed=True))
# Removing reflection is a deliberate invalid substitute for the theorem's presentation.
a,b,total=matrices(15,(2,2),(1,1),False)
assert total-rank(a)!=18 and total-rank(b)==18
record=dict(status='PASS',arithmetic='Independent Python integer bit rows over F2',
            cases=len(checks),checks=checks,corruption_controls=1,
            scope='Finite multivariable rank consequences in original raw rows; the all-level formula rests on the written Koszul/Kunneth proof.')
(B/'verification/multivariable-distribution-results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('PASS:',len(checks),'independent raw-row multivariable cases and one corruption control.')
