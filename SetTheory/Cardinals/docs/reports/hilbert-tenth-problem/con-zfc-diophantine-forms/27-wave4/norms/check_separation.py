#!/usr/bin/env python3
"""Exact bounded diagnostics for the stated separation proof, not semantics."""
import json, random
from pathlib import Path
from build_two_weight_norm12 import independent_norm

HERE=Path(__file__).resolve().parent
rng=random.Random(215421)
weak_cases=500
for case in range(weak_cases):
    q=rng.randrange(16,100)
    w,s,i,T=[rng.randrange(1,8) for _ in range(4)]
    X=w*q; Y=s*q**3; E=X*Y
    R=rng.randrange(1,q**4-2); h=rng.randrange(1,8)
    epsilon=rng.choice([-1,1]); k=R+epsilon+h*E
    eta=rng.randrange(1,k); c=k*Y+eta
    a=E+Y; H=4*a+3; Delta=a*a+H
    ell=E*k*Y; A=1+ell*(ell+k); G=1+Delta*c*c
    I=i*c*c; D=1+Delta*I*I; Q=(Delta*I)**2
    v=c*T; b=c+R*D; W=2*I*(T+R*a*i*c)
    assert X>=16 and Y>=64 and a>=64 and Q>=3 and R<c
    assert 64*G<81*A                 # sqrt(G)<(9/8)sqrt(A)
    # (4/3)[v(a+2)I+b]<(3/4)W sqrt(G).
    assert 256*(v*(a+2)*I+b)**2<81*W*W*G
    assert H*W>36

fixtures=[]
for m in [2,3,5]:
    Q=m*m; d=Q-1; chi,psi=1,0
    for idx in range(1,6):
        chi,psi=m*chi+d*psi,chi+m*psi
        if idx not in [3,5]:continue
        assert chi%m==0
        V=-chi//m; y=psi
        assert Q*V*V-d*y*y==1
        for f in [2,3,5]:
            D=f*f; v=1; b=v*f-V; e=Q*(D*v*v+b*b)-1
            H=7; W=12; M=2*W; L=1+H*W
            gamma=3; b0=5; u=b0+H*gamma; tau=100
            r=gamma+W*u+M*tau+y
            S=b0+H*r
            assert S==L*u+H*M*tau+H*y
            vals=dict(G=u*u,A=tau*tau,D=D,S=S,L=L,H=H,
                      Bnd=W,d=d,e=e,Q=Q,v=v,b=b)
            assert independent_norm(vals)==0
            fixtures.append(dict(m=m,auxiliary_index=idx,f=f,passed=True))

receipt={"weak_outer_bound_cases":weak_cases,
         "exact_radical_separation_checks":True,
         "isolated_completeness_fixtures":fixtures,
         "scope":"Finite diagnostics of inequalities and norm completeness identity. Not a compiler witness or semantic proof."}
(HERE/'SEPARATION_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
