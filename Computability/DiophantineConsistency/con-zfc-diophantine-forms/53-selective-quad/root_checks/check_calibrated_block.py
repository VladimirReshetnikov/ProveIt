#!/usr/bin/env python3
"""Independent check: tune the empty block to make the threshold a square."""
import json,random
from pathlib import Path
rng=random.Random(23017)
def req(p,m):
 if not p:raise AssertionError(m)
cases=0
for k in range(1,7):
 b=2**k;kappa=4;B=2**kappa*b*b
 ws=[1,2,3];targets=[6,8];n=3;m=2;t=3;K=14;E=t+K+2;H=E+t+1+m
 N0=B**(t+1);L=2*b*B**E
 mask=N0-1-(b-1)*sum(B**w for w in ws)+N0*(B-2)*sum(B**q for q in targets)
 N=2**((kappa*H+2-m)//2)*b**(H-(n-1)//2)
 req(N*N==2**((L.bit_length()-1)+mask.bit_count()+1),'threshold square')
 req(N<=L,'threshold bound')
 for j in range(100):
  S=rng.randrange(B**E)
  req(S+mask<L,'strict block bound')
  R=L*L+(S+mask)*L+(L-1-S)
  req((R.bit_count()>=2*(N.bit_length()-1))==((S&mask)==0),'carry equivalence')
  cases+=1
out={'status':'PASS','cases':cases,'scope':'finite toy checks of exact parity-tuned block, universal argument separate'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
