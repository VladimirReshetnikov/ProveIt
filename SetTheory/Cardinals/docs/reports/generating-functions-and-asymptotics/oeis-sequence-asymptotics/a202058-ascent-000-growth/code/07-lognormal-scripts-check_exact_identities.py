#!/usr/bin/env python3
"""Exact rational checks of state identities; finite corroboration, not proof."""
from fractions import Fraction as F
import json
from pathlib import Path

def rank(s,u,k,R):
 return (min(k,s)+R*max(k-s,0))/(s+R*u)
count=0
for R in [F(1),F(3,2),F(7,4),F(2)]:
 for m in range(1,17):
  for s in range(m):
   u=m-s;D=s+R*u;z=F(s)/D
   for k in range(m):
    r=rank(s,u,k,R);H=s+2*u
    for i in range(m):
     nu=int(i>=s);A=int(i>=k)
     ss,uu,kk=(s-1,u+A,i) if not nu else (s+1,u-(not A),i+1)
     xx=(min(i,s)+R*max(i-s,0))/D
     de=-1+(2-R)*nu+R*A;a=nu-xx*de;c=2*nu-1-z*de
     DD=ss+R*uu;rr=rank(ss,uu,kk,R);zz=F(ss)/DD
     assert DD==D+de
     assert rr-xx==a/DD
     assert zz-z==c/DD
     assert ss+2*uu-H==2*A-1
     d=xx-r+(1-A)
     assert 0<=d<1
     assert ss+2*uu-H-2*(rr-r)==1-2*d-2*a/DD
     if not nu and A:
      assert 0<=xx-rr<=F(1,8)
     else:
      assert rr>=xx
     count+=1
out={'exact_rational_cases':count,'max_m':16,'R_values':['1','3/2','7/4','2'],'passed':True,'scope':'Finite exact checks; analytic proof remains separate'}
Path(__file__).with_name('exact-identity-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
