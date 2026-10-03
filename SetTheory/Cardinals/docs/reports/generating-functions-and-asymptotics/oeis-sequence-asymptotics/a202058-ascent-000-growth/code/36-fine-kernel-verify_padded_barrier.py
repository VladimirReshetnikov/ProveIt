#!/usr/bin/env python3
"""Independent numerical tests, not replacements for the analytic inequalities."""
import math, json, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROOF=ROOT.parent/'padded-barrier-proof.md'
def children(x):
    s,u,k=x
    return [(s-1,u+int(i>=k),i) if i<s else (s+1,u-int(i<k),i+1) for i in range(s+u)]
def pad(x,L):
    s,u,k=x
    return s+L,u,k+L
def rank(x,R):
    s,u,k=x
    return (min(k,s)+R*max(k-s,0))/(s+R*u)
qvals=[1e-7,1e-4,.01,.1,.5,1,2,5,10,20,40,80,200,500]
maxm=26
worst={name:[-math.inf,None] for name in ['upper_residual_fraction','lower_residual_fraction','weighted_upper_fraction','weighted_lower_fraction','riemann_upper_fraction']}
count=0
for q in qvals:
    z=math.exp(-q); om=-math.expm1(-q); R=2-z
    p=.5*(q+math.log(R)); scale=math.exp(.5*q)
    # Every sum and derivative below is scaled by e^(q/2).
    bscaled=math.sqrt(R)*om/q
    for m in range(1,maxm+1):
      for s in range(m):
       u=m-s; D=s+R*u
       for k in range(m):
        x=(s,u,k); r=rank(x,R)
        dr=(-k*u if k<=s else -s*(m-k))/(D*D)
        lam=D*bscaled/R
        deriv=lam-bscaled*(r+q*z*dr)
        actual=frozen=0.
        for i,y in enumerate(children(x)):
          ss,uu,kk=y
          assert ss>=0 and uu>=1 and 0<=kk<ss+uu
          rr=rank(y,R); ri=(min(i,s)+R*max(i-s,0))/D
          weight=p*(ss-s)+q*(uu-u)-.5*q
          actual+=math.exp(weight+q*(r-rr))
          frozen+=math.exp(weight+q*(r-ri))
          assert abs(rr-ri)*D<=4+1e-10
          if i<s and i>=k:
            assert -1e-12<=ri-rr<=1/D+1e-10
          else: assert rr-ri>=-1e-12
        tol=2e-7*(1+lam+frozen+actual)
        assert frozen+tol>=lam
        assert frozen-lam<=3*math.sqrt(2)+tol
        assert actual<=math.exp(q/D)*frozen+tol
        assert actual+tol>=math.exp(-4*q/D)*lam
        ub=q*math.exp(q/D)+3*math.sqrt(2)*(q+1)*math.exp(q/D)+1
        lb=4*q+1
        assert (actual-deriv)/bscaled <=ub+tol/bscaled
        assert (deriv-actual)/bscaled <=lb+tol/bscaled
        vals={'upper_residual_fraction':(actual-deriv)/(bscaled*ub),'lower_residual_fraction':(deriv-actual)/(bscaled*lb),'weighted_upper_fraction':actual/(math.exp(q/D)*frozen),'weighted_lower_fraction':math.exp(-4*q/D)*lam/actual,'riemann_upper_fraction':(frozen-lam)/(3*math.sqrt(2))}
        for name,v in vals.items():
          if v>worst[name][0]:worst[name]=[v,[q,s,u,k]]
        count+=1
padding=0
for m in range(1,maxm+1):
 for s in range(m):
  for k in range(m):
   x=(s,m-s,k)
   for L in [0,1,2,5,20]:
    original=children(x); padded=children(pad(x,L))
    assert padded[L:]==[pad(y,L) for y in original]
    padding+=len(original)
result={'scope':'Independent finite tests only. Analytic audit is audit-padded-barrier.md.','proof_sha256':hashlib.sha256(PROOF.read_bytes()).hexdigest(),'q_values':qvals,'max_m':maxm,'residual_state_cases':count,'mapped_transitions_tested':padding,'worst_fractions':worst,'all_assertions_passed':True}
(ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
