#!/usr/bin/env python3
"""Exact parameter arithmetic and numerical Fourier-frame checks for the rank theorem."""
from fractions import Fraction
from pathlib import Path
import json
import numpy as np

ROOT=Path(__file__).resolve().parents[1]

def ceil_fraction(x):
    return -((-x.numerator)//x.denominator)

def rank_bounds(d,s,u,v):
    a,z=1-u,1+v
    return a*s<=d, max(ceil_fraction(a*s),ceil_fraction(a*a*d/z))

def construct(d,s,u,v,r):
    a=1-u;k=ceil_fraction(a*s)
    lam=[Fraction(1)]*(k-1)+[a*s-k+1]
    Q=np.exp(2j*np.pi*np.outer(np.arange(r),np.arange(r))/r)/np.sqrt(r)
    E=np.zeros((r,s),complex)
    for j,x in enumerate(lam):E[j,j]=np.sqrt(float(x))
    B=np.zeros((d,s),complex);B[:r]=Q@E
    M=np.zeros((d,d),complex);moment=0.
    for j in range(r):
        diag=np.r_[np.exp(2j*np.pi*j*np.arange(r)/r),np.ones(d-r)]
        RB=diag[:,None]*B
        M+=RB@RB.conj().T/r
        moment+=d*np.linalg.norm(B.conj().T@RB,'fro')**2/r
    target=np.diag(np.r_[np.full(r,float(a*s/r)),np.zeros(d-r)])
    eig=np.linalg.eigvalsh(B.conj().T@B)
    deficit=np.maximum(1-eig,0).sum()
    assert np.max(eig)<=1+1e-10 and np.min(eig)>=-1e-10
    assert abs(deficit-float(u*s))<1e-9
    assert np.linalg.norm(M-target,'fro')<1e-9
    assert abs(moment-float(d*(a*s)**2/r))<1e-7
    assert moment<=float((1+v)*s*s)+1e-7
    assert np.linalg.matrix_rank(M,tol=1e-9)==r
    return {"d":d,"s":s,"u":str(u),"v":str(v),"r":r,
            "rank_B":k,"second_moment":moment,"second_moment_cap":float((1+v)*s*s),
            "covariance_residual":float(np.linalg.norm(M-target,'fro')),
            "subspace_condition_certificate":"sum_j (1-eigenvalue_j(B*B))_+ = u*s"}

checks=[];infeasible=[]
for d,s,u,v in [(5,3,Fraction(1,3),Fraction(1,2)),
                (7,6,Fraction(1,4),Fraction(1,5)),
                (4,4,Fraction(0),Fraction(0)),
                (1,2,Fraction(1,2),Fraction(0)),
                (100,90,Fraction(1,10),Fraction(1,5)),
                (100,10,Fraction(1,10),Fraction(1,5)),
                (100,120,Fraction(1,10),Fraction(1,5))]:
    feasible,lo=rank_bounds(d,s,u,v)
    if not feasible:
        infeasible.append({"d":d,"s":s,"u":str(u),"v":str(v),"a_s":str((1-u)*s)})
        continue
    for r in sorted(set([lo,d,(lo+d)//2])):
        checks.append(construct(d,s,u,v,r))
out={"status":"PASS","scope":"Exact rational rank thresholds and floating-point checks of explicit Fourier constructions; the paper supplies the proofs.","checks":checks,"infeasible_examples":infeasible}
(ROOT/'checks/rank_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({"status":"PASS","construction_checks":len(checks),"infeasible_examples":infeasible},indent=2))
