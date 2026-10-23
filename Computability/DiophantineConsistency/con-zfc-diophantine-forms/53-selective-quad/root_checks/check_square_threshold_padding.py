#!/usr/bin/env python3
"""Independent exact toy audit of the harmless high-mask parity adjustment."""
import json,random
from pathlib import Path

def req(p,m):
 if not p:raise AssertionError(m)
rng=random.Random(20261023)
cases=0
for k in range(1,5):
 b=2**k;kappa=4;B=2**kappa*b*b
 weights=[1,2,3];targets=[6,8];n=len(weights);m=len(targets)
 t=max(weights);K=max(targets)+2*t;E=t+K+3;H=E+t+1+m
 N0=B**(t+1);L=B**E
 Tlow=N0-1-(b-1)*sum(B**w for w in weights)
 T0=Tlow+N0*(B-2)*sum(B**q for q in targets)
 high=N0*B**(K+1)
 T=T0+(2*b-1)*high
 N=2**((kappa*H+2-m)//2)*b**(H-(n-1)//2)
 req(N*N==2**((L.bit_length()-1)+T.bit_count()+1),'square threshold identity')
 for j in range(100):
  S=rng.randrange(high)
  req(S+T<L,'no overflow')
  req((S&T)==(S&T0),'harmless high mask')
  R=L*L+(S+T)*L+(L-1-S)
  req((R.bit_count()>=2*(N.bit_length()-1))==((S&T0)==0),'binomial valuation')
  cases+=1
out={'status':'PASS','cases':cases,'k_range':[1,4],'scope':'finite exact toy checks, not an unbounded theorem'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
