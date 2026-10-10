#!/usr/bin/env python3
"""Independent exact finite matrices for raw and shuffle-lifted Cayley laws.

No imports from the older report's word code. Arithmetic is integer,
with gcd normalization during Gaussian elimination over Q.
"""
from itertools import product,combinations
from collections import Counter
from math import gcd
from functools import reduce
import json,time

# Z=dt/t; C=dt/(1-t); A=i dt/(1-it); B=-dt/(1+t); D=-i dt/(1+it).
Z,C,A,B,D=range(5)
T=[{C:1,B:-1},{Z:1,B:1},{B:1,D:-1},{B:1},{B:1,A:-1}]
K=[Z,C,D,B,A]

def words(n):
    if n==0:return [()]
    return [w for w in product(range(5),repeat=n) if w[0]!=C and w[-1]!=Z]

def con(w):return tuple(K[x] for x in w)

def cayley(w):
    out=Counter()
    choices=[list(T[x].items()) for x in reversed(w)]
    for choice in product(*choices):
        v=tuple(x for x,c in choice)
        coeff=1
        for x,c in choice:coeff*=c
        out[v]+=coeff
    return {v:c for v,c in out.items() if c}

def raw(w):
    row=Counter({w:1})
    for v,c in cayley(w).items():row[v]-=c
    return {v:c for v,c in row.items() if c}

def shuf(u,v):
    out=Counter();n=len(u)+len(v)
    for choices in combinations(range(n),len(u)):
        chosen=set(choices);it_u=iter(u);it_v=iter(v)
        w=tuple(next(it_u) if j in chosen else next(it_v) for j in range(n))
        out[w]+=1
    return out

def lift(row,v):
    out=Counter()
    for u,c in row.items():
        for w,m in shuf(u,v).items():out[w]+=c*m
    return {w:c for w,c in out.items() if c}

def project(row,parity):
    if parity=='all':return row
    out=Counter()
    for w,c in row.items():
        v=con(w)
        if w==v:
            if parity=='even':out[w]+=c
        elif w<v:out[w]+=c
        else:out[v]+=c if parity=='even' else -c
    return {w:c for w,c in out.items() if c}

def primitive(row):
    if not row:return row
    g=reduce(gcd,row.values())
    if row[min(row)]<0:g=-g
    return {j:c//g for j,c in row.items()}

def rank(rows,parity):
    pivots={}
    for row in rows:
        row=primitive(project(row,parity))
        while row:
            j=min(row)
            if j not in pivots:pivots[j]=row;break
            p=pivots[j];a,b=row[j],p[j];g=gcd(a,b);a//=g;b//=g
            out={h:c*b for h,c in row.items()}
            for h,c in p.items():out[h]=out.get(h,0)-a*c
            row=primitive({h:c for h,c in out.items() if c})
    return len(pivots)

def series(N):
    # H^2 = H(t^2)*(1-t)/(1-5t).
    h=[1]+[0]*N;b=[1]+[4*5**(n-1) for n in range(1,N+1)]
    for n in range(1,N+1):
        v=sum(h[j//2]*b[n-j] for j in range(0,n+1,2))-sum(h[k]*h[n-k] for k in range(1,n))
        assert v%2==0;h[n]=v//2
    # G^2=H(t^2)*(1-t)^2/((1+t)*(1-3t)).
    b=[1]+[0]*N
    for n in range(1,N+1):b[n]=2*b[n-1]+(3*b[n-2] if n>=2 else 0)+(-2 if n==1 else 1 if n==2 else 0)
    g=[1]+[0]*N
    for n in range(1,N+1):
        v=sum(h[j//2]*b[n-j] for j in range(0,n+1,2))-sum(g[k]*g[n-k] for k in range(1,n))
        assert v%2==0;g[n]=v//2
    return h,g,[(a-b)//2 for a,b in zip(h,g)]

def main():
    start=time.monotonic();receipts=[];h,g,imag=series(12)
    for n in range(1,5):
        ws=words(n);rows=[raw(w) for w in ws]
        # The independent transform squares to identity, and commutes with conjugation.
        for w in ws:
            rr=Counter()
            for u,c in cayley(w).items():
                for v,m in cayley(u).items():rr[v]+=c*m
            assert {v:c for v,c in rr.items() if c}=={w:1}
            assert {con(v):c for v,c in cayley(w).items()}==cayley(con(w))
        lifts=[lift(raw(u),v) for k in range(1,n+1) for u in words(k) for v in words(n-k)]
        dim_odd=sum(w<con(w) for w in ws)
        raw_all=rank(rows,'all');raw_odd=rank(rows,'odd')
        ideal_all=rank(lifts,'all');ideal_odd=rank(lifts,'odd')
        expected_raw=0 if n==1 else 4*5**(n-2)-3**(n-2)-(2*5**((n-3)//2) if n%2 else 0)
        assert raw_odd==expected_raw
        assert ideal_all==len(ws)-h[n]
        assert ideal_odd==dim_odd-imag[n]
        receipt={'weight':n,'admissible_words':len(ws),'imaginary_coordinates':dim_odd,
                 'raw_all_rank':raw_all,'raw_imaginary_rank':raw_odd,
                 'lifted_row_instances':len(lifts),'ideal_all_rank':ideal_all,
                 'ideal_imaginary_rank':ideal_odd,'ideal_quotient_dimension':h[n],
                 'ideal_imaginary_quotient_dimension':imag[n]}
        receipts.append(receipt);print(json.dumps(receipt),flush=True)
    result={'result':'PASS','arithmetic':'exact integers and gcd; rational rank',
            'matrices':receipts,'hilbert_total':h,'hilbert_conjugation_trace':g,
            'hilbert_imaginary':imag,'seconds':time.monotonic()-start}
    with open('cayley_ranks_verified.json','w') as f:json.dump(result,f,indent=2);f.write('\n')
if __name__=='__main__':main()
