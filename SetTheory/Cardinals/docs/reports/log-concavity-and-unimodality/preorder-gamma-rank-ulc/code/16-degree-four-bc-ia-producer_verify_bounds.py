from fractions import Fraction as Q
from math import comb
import json,itertools
from pathlib import Path
D=Path(__file__).parent
rows=[];exceptions=[]
for m in range(2,5):
 for n in range(m,5):
  for r in range(min(m,m+n-4)+1):
   v=m*n-r;K=20*Q(v*(m+n),m*n)-16*(m+n)-8
   if K < -12:
    assert m+n-r==4
    bound=3*v*v+K*comb(m,2)
    assert bound>0
    exceptions.append({'m':m,'n':n,'r':r,'v':v,'K':str(K),'d_upper':comb(m,2),'E_lower':str(bound)})
  r=min(m,m+n-4);v=m*n-r;K=20*Q(v*(m+n),m*n)-16*(m+n)-8
  rows.append([m,n,r,str(K)])
assert [(e['m'],e['n'],e['r']) for e in exceptions]==[(2,4,2),(3,4,3),(4,4,4)]
for A,B,Z in itertools.product(range(25),repeat=3):
 p1=A+B+2*Z;p2=A*B+(A+B)*Z+comb(Z,2);N=A+B+Z
 lhs=6*N*p1-20*p2;rhs=(A+B-Z)**2+Z*Z+5*(A-B)**2+10*Z
 assert lhs==rhs and lhs>=0
r={'small_count_rows':rows,'exceptions':exceptions,'pair_identity_integer_checks':25**3,'status':'all exact checks passed'}
(D/'bound_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
