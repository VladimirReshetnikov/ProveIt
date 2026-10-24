#!/usr/bin/env python3
"""Independent exact finite diagnostics for the refined shared Pell certificate.
The universal proof is the adjacent review, not this finite experiment.
"""
import json
from pathlib import Path

def pell(a,k,mod=None):
    d=a*a-1
    def mul(v,w):
        x=v[0]*w[0]+d*v[1]*w[1]
        y=v[0]*w[1]+v[1]*w[0]
        return (x,y) if mod is None else (x%mod,y%mod)
    out=(1,0); p=(a,1)
    while k:
        if k&1:out=mul(out,p)
        p=mul(p,p);k//=2
    return out

def require(b,msg):
    if not b:raise ValueError(msg)

def norm(a,x,y):return x*x-(a*a-1)*y*y-1

def trial(calls):
    W=sum(n+k for n,k in calls)
    sum_m=sum(n**k for n,k in calls)
    ar=1
    while True:
        A,z0=pell(W+1,W*ar)
        if A>=sum_m+2:break
        ar+=1
    global_gap=A-sum_m-2
    require(global_gap>=0,'global output gap')
    require(z0%W==0,'bounding divisibility')
    Z=z0//W
    pair={k:pell(A,k) for _,k in calls}
    P=1
    for x,y in pair.values():P*=y
    M=4*P*P
    x,y=1,0
    d=A*A-1
    for L in range(1,2000001):
        x,y=(A*x+d*y)%M,(x+A*y)%M
        if (x,y)==(1,0):break
    else:raise ValueError('diagnostic period budget exceeded')
    U,V=pell(A,L)
    require(V%M==0 and V>0,'shared divisibility')
    v=V//M
    t=((A-1)*pow(4*P,-1,U))%U
    while t<1 or 1+4*P*t<=A:t+=U
    B=1+4*P*t;b=t-1
    require(norm(W+1,A,W*Z)==0,'bound norm')
    require(norm(A,U,V)==0,'common Pell norm')
    require(V==4*P*P*v,'V definition')
    require(B==1+4*P*(b+1),'B definition')
    require((B-A)%U==0,'CRT')
    for k,(X,Y) in pair.items():
        S,R=pell(B,k)
        require(Y>=k>0,'index bound')
        require(norm(A,X,Y)==0 and norm(B,S,R)==0,'private norms')
        require(S>=X and R>=k,'nonnegative progression quotients')
        require((S-X)//U>=0 and (R-k)//(4*Y)>=0,'progression quotients')
        require((S-X)%U==0,'X congruence')
        require((R-k)%(4*Y)==0,'Y congruence')
    for n,k in calls:
        m=n**k;T=2*A*n-n*n-1
        X,Y=pair[k]
        require(T>=A>m,'strict power gap from common A')
        require((X+Y*n-Y*A-m)%T==0,'power congruence')
        # Changing m while retaining T, with its positive bound still true,
        # must violate the congruence. This checks an actual discriminating row.
        require((X+Y*n-Y*A-(m+1))%T!=0,'power-output mutation')
    require(norm(W+1,A,-W*Z)==0 and norm(A,U,-V)==0,'signed norm coordinates')
    return {'calls':calls,'W':W,'A':A,'distinct_exponents':len(pair),'period_L':L,
            'U_bits':U.bit_length(),'B_bits':B.bit_length(),'status':'PASS'}

if __name__=='__main__':
    records=[trial(c) for c in [[(1,1)],[(1,1),(2,1)],[(1,2)]]]
    result={'scope':'exact finite diagnostics, not the universal semantic proof','trials':records}
    path=Path(__file__).with_name('REFINED_BATCH_FINITE_CHECKS.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
