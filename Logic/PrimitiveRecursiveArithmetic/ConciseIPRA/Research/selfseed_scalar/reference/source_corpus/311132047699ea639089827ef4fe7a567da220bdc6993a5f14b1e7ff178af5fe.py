# Independent diagnostic adapted from the generated-assumptions raw decoder.
# The checker never imports this file. See reference/LICENSE.txt.
"""Independent finite falsification attempt for the arithmetic-insertion lemma."""
import json, math, random
rng=random.Random(149426)
class Budget(Exception): pass
class Ctx:
 def __init__(self):self.k=0
 def i(self,a,t=None,d=0):
  if isinstance(a,list):return [self.i(b,t,d+b' \2\1\4'[len(a)]) for b in a]
  return a if self.k<=a<d else d%2 and self.i(t,d=1)
 def generate(self,s):
  n,a,u=s
  return [s,self.i(u,[list(*n),a,u],1) if n else a]
def val(t,rho,params,budget):
 budget[0]-=1
 if budget[0]<0:raise Budget
 if isinstance(t,list):
  if not t:return 0
  if len(t)==1:return 1+val(t[0],(0,)+rho,params,budget)
  if len(t)==2:return 0
  if len(t)!=3:raise ValueError
  n,a,u=t
  count=val(n,(0,0)+rho,params,budget)
  state=val(a,(0,0)+rho,params,budget)
  if count>300:raise Budget
  for _ in range(count):state=val(u,(state,state)+rho,params,budget)
  return state
 j=math.floor(t)
 if j<0:return params[j]
 if j==0:return 0
 return rho[(j-1)//2]
leaves=[0,0.0,False,0.5,1,True,1.5,2,3,4,5,6,7,8,-1,-1.5,-2,-3,math.inf,-math.inf,math.nan]
def term(d):
 if d==0 or rng.random()<.5:return rng.choice(leaves)
 return [term(d-1) for _ in range(rng.randrange(4))]
counts={'attempted':0,'accepted':0,'evaluated':0,'budget_skips':0,'counterexamples':0}
for oldfloor in (0,-1,-3):
 for _ in range(200000):
  c=Ctx();c.k=oldfloor
  n=rng.choice([0,[],False,0.0,[term(2)],[term(1),term(1)],term(1)])
  source=[n,term(3),term(3)]
  counts['attempted']+=1
  try:h=c.generate(source)
  except (TypeError,ValueError,IndexError,RecursionError):continue
  c.k-=1
  try:h=c.i(h,0)
  except (TypeError,ValueError,IndexError,RecursionError):continue
  counts['accepted']+=1
  params={j:2-j for j in range(oldfloor,0)};params[c.k]=0
  try:a=val(h[0],(),params,[10000]);b=val(h[1],(),params,[10000])
  except Budget:counts['budget_skips']+=1;continue
  counts['evaluated']+=1
  if a!=b:
   counts['counterexamples']+=1
   print('COUNTEREXAMPLE',oldfloor,source,h,a,b)
   raise SystemExit(1)
print(json.dumps(counts,indent=2))
from pathlib import Path
(Path(__file__).resolve().parents[1] / "evidence" / (Path(__file__).stem + ".json")).write_text(json.dumps(counts,indent=2)+'\n')
