"""Exact rational/integer certificate checks (standard library only)."""
from math import comb, gcd, isqrt
from fractions import Fraction
from pathlib import Path
import json

W = {
152:(2,6,1,2),244:(2,6,3,2),300:(2,4,3,2),451:(3,3,1,2),
472:(2,6,1,2),588:(2,4,3,2),628:(2,6,3,2),859:(3,3,1,1),
867:(3,3,2,2),1083:(17,0,8,1),1147:(3,3,1,2),1483:(3,3,1,1),
2467:(3,3,1,1),2707:(3,3,1,1)}
DATA = json.loads(Path(__file__).with_name('polynomials.json').read_text())

def forms(D):
    for a in range(1,isqrt(D//3)+1):
        for b in range(-a,a+1):
            c,r=divmod(b*b+D,4*a)
            if not r and c>=a and gcd(gcd(a,abs(b)),c)==1:
                if b<0 and (abs(b)==a or a==c): continue
                yield a,b,c

def valuation(n,p):
    if not n:
        return float('inf')
    v=0
    while n%p==0:
        n//=p
        v+=1
    return v

def fact_val(k,p):
    v=0
    while k:
        k//=p
        v+=k
    return v

def composition(coeff,A,B):
    result=[]
    for a in coeff[::-1]:
        new=[0]*(len(result)+1)
        new[0]=a
        for k,x in enumerate(result):
            new[k]+=A*x
            new[k+1]+=B*x
        result=new
    return result

def check():
    total=0
    for D,(p,v,u,m) in W.items():
        a=DATA[str(D)]
        h=len(a)-1
        assert a[-1]==1 and a[0]!=0 and len(list(forms(D)))==h
        A,B=p**v*u,p**(v+m)
        transformed=[sum(comb(j,k)*a[j]*A**(j-k)*B**k
                         for j in range(k,h+1)) for k in range(h+1)]
        assert transformed==composition(a,A,B)
        assert all(c%B**h==0 for c in transformed)
        assert transformed[-1]==B**h
        lo=max(m*i-fact_val(i,p) for i in range(h))
        k=h
        assert m>Fraction(1,p-1)
        while m*k-Fraction(k-1,p-1)<=lo:
            assert m*k-fact_val(k,p)>lo
            k+=1
        vals=[valuation(c,p)-v*h-m*i for i,c in enumerate(transformed)]
        print(-D,h+1,(p,v,u,m),vals)
        total+=len(a)
    print('Certified exact supports on 14 orders;',total,'transformed coefficients.')

if __name__=='__main__': check()
