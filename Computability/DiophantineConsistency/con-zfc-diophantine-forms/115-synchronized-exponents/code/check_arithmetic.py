"""Finite controls for the new shared-radius integration; not universal proofs."""
from math import comb,factorial
from pathlib import Path
from hashlib import sha256
import json

def need(ok,label):
    if not ok: raise ValueError(label)

census={}
count=0
for rho in range(1,65):
    for n in range(1,65):
        bound=(rho+1)**n
        for j in range(n+1):
            need(comb(rho+n,j)<=bound,('uniform coefficient',rho,n,j))
            count+=1
census['uniform_coefficient_cases']=count
count=0
for n in range(0,11):
    K=factorial(n)
    candidates=set(range(0,513))|{max(0,K-1),K,K+1,2*K}
    for F in sorted(candidates):
        rho=F*F;C=comb(rho+n,n);V=(rho+1)**n
        need(((V+C-1)//C==F)==(F==K),('squared fixed point',n,F))
        count+=1
census['squared_fixed_point_cases']=count
count=0
for H in range(1,16):
    T=factorial(H);rho=T*T
    for n in range(0,H+1):
        C=comb(rho+n,n);V=(rho+1)**n
        F=factorial(n);r=V+C-C*F-1;s=C-r-1
        need(r>=0 and s>=0 and V+C==C*F+r+1 and C==r+s+1,('common radius',H,n))
        count+=1
census['shared_radius_exact_remainders']=count
count=0
for R in range(4,70):
    H=R**4
    need(4*R*(R+2)<=H,('majorant basic',R))
    for t in range(1,R+1):
        for k in range(1,R+1):
            need(k*(t+2)*(H+1)<H*H,('radix exponent comparison',R,t,k))
            count+=1
census['remaining_radix_exponent_cases']=count
need(comb(1+8,4)<=2**8,'rho smaller than n fixture')
# A counterexample to using an absent rho>=1 hypothesis: rho=0,n=4,j=2.
need(comb(4,2)>1,'zero-radius counterexample must be detected')
# The centered formula was independently rederived but is an existing arrival.
count=0
for n in range(0,11):
    K=factorial(n)
    for F in sorted(set(range(0,129))|{max(0,K-1),K,K+1}):
        V=(2*F+n+1)**n;D=2**n*comb(F+n,n)
        need((V//D==F)==(F==K),('inherited centered identity',n,F))
        count+=1
census['inherited_centered_identity_cases']=count
result={'status':'PASS','scope':'Finite exact integer controls only. Universal proofs are in SHARED_SQUARE_PROOF.md; these checks do not establish calibration or consistency.','cases':census,'required_hypothesis_counterexample':{'rho':0,'n':4,'j':2,'binomial':6,'invalid_bound':1},'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
out=Path(__file__).resolve().parents[1]/'checks/ARITHMETIC_CONTROLS.json'
out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps(result,indent=2))
