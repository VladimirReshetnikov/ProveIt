"""Exact algebraic regressions for the tanh-circle reduction.

These checks supplement, and do not replace, the analytic selection proof.
Uses only the Python standard library for coefficient identities.
"""
from fractions import Fraction as F
from math import comb, factorial
import hashlib, json
from pathlib import Path

LIMIT=40

def mul(a,b):
    c=[F(0)]*min(LIMIT+1,len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:len(c)-i]):
                if y:c[i+j]+=x*y
    return c

def powers(a,n):
    out=[[F(1)]]
    for _ in range(n):out.append(mul(out[-1],a))
    return out

log=[F(0)]+[F((-1)**(j+1),j) for j in range(1,LIMIT+1)]
atanh=[F(0)]+[F(1,j) if j%2 else F(0) for j in range(1,LIMIT+1)]
logs=powers(log,6); ats=powers(atanh,6)
hashval=hashlib.sha256(); count=zeros=0
for d in range(1,7):
    oneplus=[F(comb(2*d,j)) for j in range(2*d+1)]
    for k in range(8):
        twoplus=[F(comb(k,j)*2**(k-j)) for j in range(k+1)]
        left=mul(mul(twoplus,oneplus),logs[d])
        for q in range(9):
            M=k+2*d+q+1
            oneminus=[F(comb(q,j)*(-1)**j) for j in range(q+1)]
            right=mul(mul(oneplus,oneminus),ats[d])
            a=left[M]
            b=right[M]/2**(d+q+1)
            if a!=b:raise RuntimeError((d,k,q,a,b))
            H=a*factorial(M)/factorial(d)
            if H.denominator!=1:raise RuntimeError(('noninteger',d,k,q,H))
            zeros+=H==0;count+=1
            hashval.update(f'{d},{k},{q}:{H}\n'.encode())
print('Exact coefficient identities:',count)
print('Exact zero cases:',zeros)
print('SHA256:',hashval.hexdigest())

Path(__file__).with_name("tanh_identity_checks.json").write_text(json.dumps({"status":"PASS","cases":count,"zero_cases":int(zeros),"sha256":hashval.hexdigest(),"scope":"Exact finite coefficient identity regression; the analytic proof is independent"},indent=2)+"\n")
