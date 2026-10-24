#!/usr/bin/env python3
"""Independent exact reconstruction, without SymPy or sampled inequalities."""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import json
from poly import add,sub,scale,mul,power,mon,shift,weight

ROOT=Path(__file__).resolve().parent
def require(p,msg):
    if not p:raise ValueError(msg)
def read(name):
    d=json.loads((ROOT/'data'/name).read_text())
    return {tuple(t['powers']):t['coefficient'] for t in d['terms']}

def audit():
    one=mon((0,0,0,0));A,C,i,Z=[mon(tuple(int(j==k) for j in range(4))) for k in range(4)]
    J=sub(scale(A,4),scale(one,5));am1=sub(power(A,2),one)
    D=add(mul(am1,power(C,2)),one);e=mul(mul(i,J),C)
    F=add(mul(mul(power(e,2),D),sub(D,one)),one)
    G=add(A,mul(F,sub(add(mul(C,D),one),A)))
    H=add(C,mul(F,Z));I=add(mul(sub(power(G,2),one),power(H,2)),one)
    Q=mul(mul(D,F),I)
    require(max(m[0] for m in Q)==36,'radicand degree in A')
    q=defaultdict(dict)
    for m,c in Q.items():q[m[0]][m[1:]]=c
    t={18:mon((19,5,1),1024)}
    require(power(t[18],2)==q[36],'formal leading square')
    for k in range(1,19):
        cross=add(*(mul(t[18-j],t[18-k+j]) for j in range(1,k)))
        num=sub(q.get(36-k,{}),cross)
        t[18-k]={tuple(a-b for a,b in zip(m,(19,5,1))):Fraction(c,2048) for m,c in num.items()}
    P0={}
    for a,p in t.items():
        for m,c in p.items():
            ex=(a,m[0]+5,m[1]+1,m[2]);co=1024*c
            require(all(x>=0 for x in ex) and co.denominator==1,'polynomial denominator clearing')
            P0[ex]=int(co)
    require(P0==read('saturated_P.json'),'all formal majorant coefficients')
    correction=mon((0,24,6,1),297874)
    P=add(P0,correction);require(P==read('saturated_corrected_P.json'),'corrected majorant')
    sigma=mon((0,5,1,0),1024)
    raw_defect=sub(power(P0,2),mul(power(sigma,2),Q))
    require(raw_defect==read('saturated_defect.json'),'uncorrected defect identity')
    defect=sub(power(P,2),mul(power(sigma,2),Q))
    cert=shift(defect,(3,1,1,1))
    require(cert==read('saturated_corrected_certificate.json'),'whole shifted certificate')
    require(all(c>0 for c in cert.values()),'every nonzero defect coefficient positive')
    require(cert.get((0,0,0,0))==8341416066461366340,'strict boundary certificate')
    ps=shift(P0,(3,1,0,0))
    require(all(c>0 for c in ps.values()) and ps.get((0,0,0,0),0)>0,'majorant positivity')
    weights=(16385,1,1,7943)
    pdeg=weight(P,weights);ddeg=weight(defect,weights)
    require(pdeg==302903 and ddeg==310876,'cancellation-aware weighted degrees')
    topP={m:c for m,c in P.items() if sum(a*b for a,b in zip(m,weights))==pdeg}
    topD={m:c for m,c in defect.items() if sum(a*b for a,b in zip(m,weights))==ddeg}
    require(topP=={(18,24,6,1):1048576},'unique majorant leading monomial')
    require(topD=={(18,48,12,2):2*297874*1048576},'unique defect leading monomial')
    # A finite identity error is detectable, independently of circuit size.
    broken=P.copy();broken[(0,0,0,0)]=broken.get((0,0,0,0),0)+1
    require(sub(power(broken,2),mul(power(sigma,2),Q))!=defect,'coefficient corruption rejected')
    # The uncorrected approximation is a concrete negative control.
    require(shift(raw_defect,(3,1,1,1))[(0,0,0,0)]<0,'uncorrected boundary is invalid')
    return dict(status='PASS',radicand_terms=len(Q),polynomial_terms=len(P),
                positive_majorant_terms=len(ps),defect_certificate_terms=len(cert),
                certificate_constant=cert[(0,0,0,0)],majorant_degree=pdeg,defect_degree=ddeg,
                formal_recurrence_steps=18,negative_controls=2)

if __name__=='__main__':
    out=audit();print(json.dumps(out,indent=2))
