#!/usr/bin/env python3
"""Finite independent regression checks of the common universal proof identities."""
from pathlib import Path
from itertools import product
import json,random
ROOT=Path(__file__).resolve().parent

def need(x,m):
 if not x:raise ValueError(m)
def v2factorial(n):
 out=0
 while n:n//=2;out+=n
 return out

def main():
 blocks=borrows=thresholds=masks=mods=0
 for u in range(1,8):
  L=1<<u
  for S in range(L):
   for T in range(L-S):
    for top in [1,3,10]:
     X=top*L*L+(S+T)*L+L-1-S
     deficit=S.bit_count()+T.bit_count()-(S+T).bit_count()
     target=u+T.bit_count()+top.bit_count()
     need(X.bit_count()==target-deficit,'Two-block identity')
     need(v2factorial(2*X)-2*v2factorial(X)==X.bit_count(),'Central binomial valuation')
     need((X.bit_count()>=target)==(S&T==0),'Exact carry threshold')
     blocks+=1
 B=64;targets={1,3};mask=sum((B-2)*B**j for j in targets)
 for low in product(range(-3,4),repeat=4):
  hs=low+(1,);J=sum((2*h+int(j in targets))*B**j for j,h in enumerate(hs))
  need(0<J<B**5,'Fixture bounds')
  need((J&mask==0)==all(hs[j]==0 for j in targets),'Signed-borrow target iff')
  borrows+=1
 for W in [31,163,170,174]:
  for K in [4000,4420,4426,4421]:
   for kap in [20,864026]:
    E=K+W+2;V=K+2*W+25
    for k in [0,1,2,3,7,20]:
     v=kap+2*k;exponent=V*v-30*k-20
     if K%2==0:q=(K+2*W+10)//2;constant=15*kap//2-10;actual=2*(constant+q*v)
     else:q=(K+2*W+9)//2;constant=8*kap-10;actual=2*(constant+k+q*v)
     need(exponent==actual,'Natural polynomial-square calibration')
     integer=V*v-31*k-21
     need(integer==kap*V-21+(2*V-31)*k,'Integer nonsquare calibration');thresholds+=1
 for b in [1,2,4,8]:
  B=16*b*b;W=4;weights=[0,2,4];N0=B**(W+1);lo=N0-1-(b-1)*sum(B**w for w in weights)
  for ds in product(range(b+2),repeat=3):
   g=sum(x*B**w for x,w in zip(ds,weights))
   need((g&lo==0)==all(x<b for x in ds),'Low digit mask');masks+=1
 for f in range(1,25):
  b=1+3*f
  for kap in [2,4,6]:
   B=(1<<kap)*b*b;E=5;L=pow(B,E);A=sum(pow(B,h)for h in range(22));ell=sum(pow(B,w)for w in range(31));N0=pow(B,32)
   T=N0-1-(b-1)*ell+N0*(B-2)*A;S=f
   X=L*L+(S+T)*L+L-1-S
   need(X%3==0,'Uncalibrated integer mod3')
   L2=b*L;X2=10*L2*L2+(S+T)*L2+L2-1-S
   need(X2%3==0,'Optional top10 mod3');mods+=1
 out=dict(status='PASS',block_and_binomial_valuation_cases=blocks,signed_borrow_cases=borrows,threshold_identities=thresholds,low_digit_mask_cases=masks,modulo_three_cases=mods,limitations='Finite diagnostics corroborate the formulas; universal arguments are in SPARSE_POPCOUNT_SOURCE_PROOF.md.')
 (ROOT/'SPARSE_POPCOUNT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
