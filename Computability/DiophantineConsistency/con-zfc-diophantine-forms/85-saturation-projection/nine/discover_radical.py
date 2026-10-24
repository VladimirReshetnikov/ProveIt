#!/usr/bin/env python3
"""Exact rational polynomial-part discovery, never needed for baseline replay."""
from collections import defaultdict
from fractions import Fraction
from functools import reduce
from math import gcd,comb
from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent

def const(c,n=4):return {(0,)*n:Fraction(c)} if c else {}
def var(k,n=4):
    a=[0]*n;a[k]=1;return {tuple(a):Fraction(1)}
def add(*xs):
    out=defaultdict(Fraction)
    for x in xs:
        for m,c in x.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def neg(x):return {m:-c for m,c in x.items()}
def sub(x,y):return add(x,neg(y))
def mul(x,y):
    out=defaultdict(Fraction)
    for m,c in x.items():
        for n,d in y.items():out[tuple(a+b for a,b in zip(m,n))]+=c*d
    return {m:c for m,c in out.items() if c}
def sq(x):return mul(x,x)
def scale(x,c,mon=None):
    if mon is None:return {m:v*c for m,v in x.items() if v*c}
    return {tuple(a+b for a,b in zip(m,mon)):v*c for m,v in x.items() if v*c}
def shift_one(x,k,h):
    out=defaultdict(int)
    for m,c in x.items():
        for j in range(m[k]+1):
            n=list(m);n[k]=j;out[tuple(n)]+=c*comb(m[k],j)*h**(m[k]-j)
    return {m:c for m,c in out.items() if c}
def write(name,p):
    rec=[{'powers':m,'coefficient':int(c)} for m,c in sorted(p.items())]
    if any(c.denominator!=1 for c in p.values()):raise ValueError('noninteger')
    (ROOT/name).write_text(json.dumps(rec,separators=(',',':'))+'\n')
def main():
    A,C,i,Z=[var(k) for k in range(4)]; one=const(1)
    J=sub(scale(A,4),const(5)); D=add(mul(sub(sq(A),one),sq(C)),one)
    e0=mul(mul(i,J),sq(C));F=add(mul(mul(sub(sq(A),one),D),sq(e0)),one)
    L=sub(add(mul(C,D),one),A); G=add(A,mul(F,L));H=add(C,mul(F,Z))
    I=add(mul(sub(sq(G),one),sq(H)),one);Q=mul(mul(D,F),I)
    print('Q terms',len(Q),flush=True)
    q=defaultdict(dict)
    for m,c in Q.items():q[m[0]][m[1:]]=c
    assert max(q)==36
    t={18:{(19,5,1):Fraction(1024)}}
    for k in range(1,19):
        rem=q[36-k]
        for ell in range(1,k):rem=sub(rem,mul(t[18-ell],t[18-k+ell]))
        t[18-k]=scale(rem,Fraction(1,2048),(-19,-5,-1))
        print('sqrt',18-k,'terms',len(t[18-k]),flush=True)
    P={(a,*m):c for a,r in t.items() for m,c in r.items()}
    den=1
    for c in P.values():den=den*c.denominator//gcd(den,c.denominator)
    mins=[min(m[k] for m in P) for k in range(4)]
    mon=tuple(max(0,-x) for x in mins)
    P=scale(P,den,mon);Qscaled=scale(Q,den**2,tuple(2*x for x in mon))
    delta=sub(sq(P),Qscaled)
    meta={'denominator':den,'scale_powers':mon,'P_terms':len(P),'P_degrees':[max(m[k] for m in P) for k in range(4)],'defect_terms':len(delta),'defect_degrees':[max(m[k] for m in delta) for k in range(4)]}
    print(meta,flush=True)
    write('radical_P.json',P);write('radical_defect.json',delta)
    pp=P
    for k,h in [(0,3),(1,1),(2,1),(3,1)]:pp=shift_one(pp,k,h)
    dd=delta
    for k,h in [(0,3),(1,1),(2,1),(3,1)]:dd=shift_one(dd,k,h)
    meta.update(P_shift_terms=len(pp),P_shift_negative=sum(c<0 for c in pp.values()),defect_shift_terms=len(dd),defect_shift_negative=sum(c<0 for c in dd.values()),defect_constant=int(dd.get((0,0,0,0),0)))
    print(meta,flush=True)
    write('radical_P_shifted.json',pp);write('radical_defect_shifted.json',dd)
    correction={(0,24,6,1):Fraction(2**20)}
    upper=add(P,correction)
    upper_defect=add(delta,scale(mul(P,correction),2),sq(correction))
    upper_shifted=upper_defect
    for k,h in [(0,3),(1,1),(2,1),(3,1)]:upper_shifted=shift_one(upper_shifted,k,h)
    write('radical_upper_P.json',upper)
    write('radical_upper_defect.json',upper_defect)
    write('radical_upper_defect_shifted.json',upper_shifted)
    meta.update(upper_terms=len(upper),upper_defect_terms=len(upper_defect),
                upper_shifted_terms=len(upper_shifted),
                upper_shifted_negative=sum(c<0 for c in upper_shifted.values()),
                upper_shifted_constant=int(upper_shifted[(0,0,0,0)]))
    (ROOT/'radical_meta.json').write_text(json.dumps(meta,indent=2)+'\n')
if __name__=='__main__':main()
