#!/usr/bin/env python3
"""Independent exact full-support certificate at the thirteen-group stage.
No external packages; evaluates all132^3 support triples using integer pair dots.
"""
from fractions import Fraction as F
from itertools import combinations,permutations
from math import lcm
import json
from pathlib import Path

ALPHA=F(321333,1000000)
OMEGA=F(2371553,1000000)
EPS=F(1,1000000)
ANCHOR_K=F(59261,103891)
ANCHOR_COST=F(26972100941,12986375000)
D=1+EPS/2
C=(OMEGA-1)/2
W=(ANCHOR_COST-2-EPS)/(ANCHOR_K-ALPHA)
V=1+EPS-ALPHA*W
SCALE=lcm(D.denominator,C.denominator,V.denominator,W.denominator)
TRIPLES=sorted(set(permutations((int(D*SCALE),int(D*SCALE),0))) |
               set(permutations((SCALE,int(V*SCALE),int(W*SCALE)))) |
               set(permutations((SCALE,int(C*SCALE),int(C*SCALE)))))
PLANS=[[[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],
[[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],
[[0,8,11,12,1],[7,10,4,3],[5,2,6,9]]]

def require(c,m):
 if not c:raise RuntimeError(m)
def dot(v,w):return sum(a*b for a,b in zip(v,w))

def supports(blocks):
 require(sorted(sum(blocks,[]))==list(range(13)),'bad partition')
 universe=set(range(13));edges=list(combinations(range(13),2))
 # Independent breadth-first traversal; order has no influence on complete max.
 ops=[tuple(map(set,blocks))]
 pending=list(blocks)
 while pending:
  b=pending.pop(0)
  if len(b)==1:continue
  h=len(b)//2;l=b[:h];r=b[h:]
  ops.append((set(l),set(r),universe-set(b)))
  pending.extend([l,r])
 rows=[]
 for A,B,O in ops:
  AB={tuple(sorted((a,b))) for a in A for b in B}
  AO={tuple(sorted((a,b))) for a in A for b in O}
  BO={tuple(sorted((a,b))) for a in B for b in O}
  for x,y,z in TRIPLES:
   rows.append(tuple(x if e in AB else y if e in AO else z if e in BO else 0 for e in edges))
 require(len(rows)==132,'supportcount')
 return rows

def certificate():
 menus=[supports(p) for p in PLANS]
 ns=[[dot(v,v) for v in menu] for menu in menus]
 dots={(i,j):[[dot(v,w) for w in menus[j]] for v in menus[i]] for i,j in combinations(range(3),2)}
 M=-1;witness=None;checked=0;countmax=0
 for a in range(132):
  for b in range(132):
   partial=ns[0][a]+ns[1][b]+2*dots[0,1][a][b]
   for c in range(132):
    value=partial+ns[2][c]+2*(dots[0,2][a][c]+dots[1,2][b][c]);checked+=1
    if value>M:M=value;witness=[a,b,c];countmax=1
    elif value==M:countmax+=1
 require(checked==132**3,'enumerationcount')
 vector=[sum(menus[i][j][e] for i,j in enumerate(witness)) for e in range(78)]
 require(dot(vector,vector)==M,'explicitwitness')
 beta2=F(2*M,SCALE*SCALE*9*169)
 require(beta2<F(1572,4225),'strictimprovement')
 return {'status':'PASS','plans':PLANS,'groups':13,'plan_count':3,
 'coefficients':list(map(str,(D,V,W,C))), 'scale':SCALE,
 'triples':[list(t)for t in TRIPLES], 'support_count':396,
 'supports_per_plan':132,'choices_checked':checked,'maximum_squared_norm':M,
 'witness':witness,'maximizer_count':countmax,'beta_squared':str(beta2)}
if __name__=='__main__':
 result=certificate()
 Path(__file__).with_name('anchored_thirteen_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k not in('plans','triples')},indent=2))
