#!/usr/bin/env python3
"""Independent exact arithmetic checks, not upstream code or a SAT solver."""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

def v2(x):
    x=F(x)
    if x==0: return None
    n,d=abs(x.numerator),x.denominator
    return (n & -n).bit_length()-(d & -d).bit_length()
def factval(n): return n-n.bit_count()
def det(a):
    a=[list(row) for row in a]; out=F(1); n=len(a)
    for j in range(n):
        k=next(k for k in range(j,n) if a[k][j])
        if k!=j: a[j],a[k]=a[k],a[j]; out=-out
        pivot=a[j][j]; out*=pivot
        for k in range(j+1,n):
            ratio=a[k][j]/pivot
            for l in range(j+1,n): a[k][l]-=ratio*a[j][l]
    return out
def require(condition):
    if not condition: raise RuntimeError("exact Cauchy regression failed")

checks=0; matrices=0
for n in range(1,7):
  for delta in (3,17,65):
    K=[[F(1,delta+2*(i-j)) for j in range(n)] for i in range(n)]
    matrices+=1
    for q in range(1,n+1):
      expected=q*(q-1)+2*sum(factval(b) for b in range(q))
      values=[]
      for rows in combinations(range(n),q):
       for cols in combinations(range(n),q):
        value=v2(det([[K[i][j] for j in cols] for i in rows]))
        require(value is not None and value>=expected)
        values.append(value); checks+=1
      require(min(values)==expected)
      principal=v2(det([row[:q] for row in K[:q]]))
      require(principal==expected)
# Actual packet normalized rows: a=8, t=2^i, z=2^(i+1)/(t+x).
residue_checks=[]
for i in range(5):
    residues=set()
    for x in range(256):
      if (x>>i)&1: continue
      d=(1<<i)+x; vd=v2(d)
      residues.add(((1<<(i+1-vd))*pow(d>>vd,-1,16))%16)
    residue_checks.append({'i':i,'residues_mod_16':sorted(residues),'missing_even_residues':sorted(set(range(0,16,2))-residues)})
require(residue_checks[0]['residues_mod_16']==[2,6,10,14])
require(residue_checks[1]['residues_mod_16']==[2,6,10,12,14])
result={'status':'passed','kind':'finite exact verification, not asymptotic proof','matrix_count':matrices,'minor_count':checks,'size_range':[1,6],'odd_delta_values':[3,17,65],'smith_slope_formula':'e_b=2b+2v2(b!)=4b-2 popcount(b)','actual_row_residue_checks':residue_checks}
path=Path(__file__).with_name('actual_cauchy_checks.json');path.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
