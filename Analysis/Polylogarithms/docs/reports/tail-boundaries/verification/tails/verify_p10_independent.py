#!/usr/bin/env python3
"""Independent Padé-sum replay of the order-ten modular certificate."""
from complete_p10 import P,bernoulli_mod,matrix_mod,det_mod
from math import factorial
from pathlib import Path
import json

a,b=5,962
B=bernoulli_mod(2*b-2)
f=[1]
for j in range(1,4*b+4): f.append(f[-1]*j%P)
fi=[pow(x,-1,P) for x in f]
mu=[B[2*r]*fi[2*r]%P for r in range(b)]
raw=[]
for i in range(a):
    n=b-a+i
    c=(2*n+1)*f[2*n+2]*fi[4*n+2]%P
    p=[2*f[2*n+2*t+1]*f[2*n+1]*fi[4*n+2]*fi[2*n-2*t+1]*fi[2*t]%P
       for t in range(n+1)]
    row=[]
    for ell in range(a):
        k=a-1-ell
        s=0
        for t in range(ell,n+1):
            ratio=f[2*t+1]*f[2*b-2*k]*fi[2*a-2*k]*fi[2*b+2*t-2*a+1]%P
            s=(s+p[t]*mu[t-ell]*(1+ratio))%P
        row.append(s*pow(c,-1,P)%P)
    raw.append(row)
A=matrix_mod(a,b,B)
assert raw==A
answer,_=det_mod(A)
epsilon=a*(b-a)+a*(a-1)//2
prefactor=(-1)**epsilon
for t in range(b): prefactor=prefactor*f[2*b+2*t-2*a+1]*fi[2*b-2*t]%P
for n in range(b-a): prefactor=prefactor*f[2*n+1]**2*fi[4*n+2]*fi[4*n+3]%P
for i in range(a):
    n=b-a+i
    prefactor=prefactor*(2*n+1)*f[2*n+2]*fi[4*n+2]%P
original=answer*prefactor%P
# An independently implemented rational Bernoulli provider is optional:
import sympy as sp
residues={}
for j in range(1,2*a):
    k=2*b-2*j
    exact=sp.bernoulli(k)
    residue=int(exact.p)%P*pow(int(exact.q)%P,-1,P)%P
    assert residue==B[k]
    residues[str(k)]=residue
result={'P':P,'a':a,'b':b,'independent_pade_sum_matches_retained_matrix':True,
        'rational_bernoulli_residues':residues,
        'source_determinant_prefactor_mod_P':prefactor,'det_M_mod_P':original,
        'det_A_mod_P':answer,'all_checks_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
