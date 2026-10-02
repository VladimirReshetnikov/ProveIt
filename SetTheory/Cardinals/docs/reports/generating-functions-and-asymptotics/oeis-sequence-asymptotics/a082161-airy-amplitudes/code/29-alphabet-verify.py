#!/usr/bin/env python3
"""Exact checks for the renewal theorem. No external dependencies."""
import json
from fractions import Fraction
from pathlib import Path

def signed(k,N):
    q=k-1; X=q*N
    b={(-1,0):1};r={}
    for x in range(X+1): b[x,0]=r[x,0]=1
    for m in range(1,N+1):
        for x in range(q*m,X+1):
            b[x,m]=2*b.get((x,m-1),0)+(m+1)*b.get((x-1,m),0)-m*b.get((x-k,m-1),0)
            r[x,m]=r.get((x,m-1),0)+(m+1)*r.get((x-1,m),0)
    return b,r

def renewal(k,N,mode='dfa',M=None):
    q=k-1;X=q*N
    a={(x,1):1 for x in range(q,X+1)}
    for m in range(1,N):
        w=[]
        for l in range(X+1):
            v=(m+1)**l
            if mode=='relaxed': w.append(v)
            else:w.append(2*v-((m+1)**(l-k+1) if l>=k and (M is None or m<M) else 0))
        for x in range(q*(m+1),X+1):
            a[x,m+1]=sum(w[l]*a.get((x-l,m),0) for l in range(x-q*m+1))
    recovered={}
    for m in range(1,N+1):
        for x in range(q*m,X+1):
            recovered[x,m]=sum((m+1)**l*a.get((x-l,m),0) for l in range(x-q*m+1))
    return a,recovered

out={'scope':'Exact signed/renewal identity and inequalities, not an amplitude proof','cases':[]}
for k in range(2,9):
    N=16;q=k-1
    b,r=signed(k,N);A,B=renewal(k,N);a,R=renewal(k,N,'relaxed')
    P=Fraction(1)
    for m in range(1,N+1):
        if m>=2:P*=1-Fraction(1,2*m**q)
        for x in range(q*m,q*N+1):
            assert b[x,m]==B[x,m] and r[x,m]==R[x,m]
            assert 2**(m-1)*P*a[x,m]<=A[x,m]<=2**(m-1)*a[x,m]
            assert 2**(m-1)*P*r[x,m]<=b[x,m]<=2**(m-1)*r[x,m]
    if k>=3:
        for M in [1,2,4,8]:
            trunc,_=renewal(k,N,M=M)
            for n in range(1,N+1):
                rat=Fraction(b[q*n,n],trunc[q*n,n])
                prod=Fraction(1)
                for j in range(M+1,n+1):prod*=1-Fraction(1,2*j**q)
                assert prod<=rat<=1
                assert 1-rat<=Fraction(1,2*(k-2)*M**(k-2))
    out['cases'].append({'k':k,'N':N,'terms':[b[q*n,n] for n in range(8)],'ratio_at_N':str(Fraction(b[q*N,N],2**(N-1)*r[q*N,N])),'lower_product':str(P),'all_assertions':'passed'})
assert out['cases'][1]['terms']==[1,1,14,532,42644,6011320,1330452032,428484011200]
assert out['cases'][2]['terms'][:6]==[1,1,30,3900,1460700,1220162880]
assert out['cases'][3]['terms'][:6]==[1,1,62,26164,43023908,199596500056]
Path(__file__).with_name('verification.json').write_text(json.dumps(out,indent=2)+'\n')
print('All exact checks passed for k=2,...,8 through 16 transient states.')
