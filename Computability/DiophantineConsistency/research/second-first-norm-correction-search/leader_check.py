#!/usr/bin/env python3
"""Independent compact-leader and fixed-port specialization check; data only."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
raw=(HERE/'RESULTS.json').read_bytes()
PIN='8a46d902b8a11c52a4dd617fb100624fc79141ecfda46b7b8158b27978b11d30'
def require(b,m):
    if not b:raise ValueError(m)
require(hashlib.sha256(raw).hexdigest()==PIN,'result pin')
r=json.loads(raw); zero=(0,)*17
# Actual symbol order: J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma,beta,K0,MC,MF.
def C(a):return {zero:a} if a else {}
def X(i):
    t=list(zero);t[i]=1;return {tuple(t):1}
def add(a,b,k=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+k*c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            q=tuple(x+y for x,y in zip(m,n));out[q]=out.get(q,0)+c*d
    return {m:c for m,c in out.items() if c}
def power(a,n):
    out=C(1)
    for _ in range(n):out=mul(out,a)
    return out
B=mul(X(13),X(0)); k=add(X(9),X(10)); C0=add(add(B,X(1),-1),X(2),-1)
D=add(mul(add(X(7),mul(B,X(14)),-1),C0),mul(B,X(1)))
compact=C(32)
for p in (power(B,20),power(k,4),power(X(3),6),power(X(5),4),
          power(X(6),6),power(X(7),2),C0,D):compact=mul(compact,p)
actual={tuple(m):c for m,c in r['variants'][0]['auxiliary_leader']}
require(compact==actual,'complete A90 compact leader')
out=[]
for index,c,betaexp in [(0,32,20),(4,-32,19)]:
    p={tuple(m):v for m,v in r['variants'][index]['auxiliary_leader']}
    mon=min(m[:13] for m in p)
    contributions=[(m,v) for m,v in p.items() if m[:13]==mon]
    require(len(contributions)==1,'unique symbolic-port contribution')
    m,v=contributions[0]
    require(v==c and m[13:]==(betaexp,0,0,0),'specialized coefficient')
    require(sum(mon)*2==r['variants'][index]['output_degree'],'output sharpness')
    out.append({'variant':index,'unknown_exponents':mon,'auxiliary_coefficient':v,
                'beta_exponent':betaexp,'output_coefficient':v*v,
                'output_beta_exponent':2*betaexp})
print(json.dumps({'scope':'data-only exact leader and specialization check',
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'result_sha256':PIN,'compact_A90_terms':len(compact),'checks':out},indent=2))
