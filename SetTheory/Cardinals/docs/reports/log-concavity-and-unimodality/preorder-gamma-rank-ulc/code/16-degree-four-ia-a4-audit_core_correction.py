from pathlib import Path
from itertools import product
from functools import lru_cache
from math import factorial,comb
import json,hashlib
D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment');O=Path(__file__).parent
R=[json.loads(x) for x in (D/'a4_polynomials.jsonl').read_text().splitlines()];r=R[9];d=len(r['types']);Q=list(map(tuple,r['quota']))
def add(p,e,c):
 if c:p[e]=p.get(e,0)+c
def clean(p):return {e:c for e,c in p.items() if c}
def mul(P,Q):
 out={}
 for e,a in P.items():
  for f,b in Q.items():add(out,tuple(x+y for x,y in zip(e,f)),a*b)
 return clean(out)
fall=[]
for n in range(5):
 p=[1]
 for j in range(n):
  z=[0]*(len(p)+1)
  for i,c in enumerate(p):z[i]-=j*c;z[i+1]+=c
  p=z
 fall.append(p)
@lru_cache(None)
def basis(q):
 den=1
 for n in q:den*=factorial(n)
 assert 24%den==0
 p={}
 for e in product(*(range(n+1) for n in q)):
  c=24//den
  for n,j in zip(q,e):c*=fall[n][j]
  if c:p[e]=c
 return p
def gamma(k,allowed):
 p={}
 for q,c in zip(Q,r['gamma'][k]):
  if c and sum(q) in allowed:
   for e,a in basis(q).items():add(p,e,c*a)
 return clean(p)
assert all(not c or sum(q) in (2,3) for q,c in zip(Q,r['gamma'][3]));assert all(not c or sum(q)==4 for q,c in zip(Q,r['gamma'][4]))
F2=gamma(2,{2});F3=gamma(3,{3});F4=gamma(4,{4});B=gamma(2,{0,1});C=gamma(3,{2})
E={}
for scalar,P,Qq in [(6,F3,C),(3,C,C),(-8,B,F4)]:
 for e,c in mul(P,Qq).items():add(E,e,scalar*c)
E=clean(E)
@lru_cache(None)
def newton_column(e):
 out=[]
 for f in product(*(range(n+1) for n in e)):
  c=1
  for n,k in zip(e,f):c*=sum((-1)**(k-j)*comb(k,j)*j**n for j in range(k+1))
  if c:out.append((f,c))
 return out
answer={}
for e,c in E.items():
 for f,a in newton_column(e):add(answer,f,c*a)
answer=clean(answer);assert all(c%576==0 for c in answer.values());answer={sum(e[i]<<(3*i) for i in range(d)):c//576 for e,c in answer.items()}
source=next(x for x in map(json.loads,(D/'core_corrections.jsonl').read_text().splitlines()) if x['id']==9);assert source['variables']==d and answer==dict(source['E']) and len(answer)==len(source['E']);assert all(c>=0 for c in answer.values())
G2=gamma(2,{0,1,2});G3=gamma(3,{2,3});whole={}
for scalar,P,Qq in [(3,G3,G3),(-8,G2,F4),(-3,F3,F3),(8,F2,F4)]:
 for e,c in mul(P,Qq).items():add(whole,e,scalar*c)
assert clean(whole)==E
result={'verdict':'template9 global gap3 approved using independently approved exterior Lorentzian lemma','template':9,'gap':3,'variables':d,'correction_nonzero_binomial_terms':len(answer),'minimum_correction_coefficient':min(answer.values()),'maximum_correction_coefficient':max(answer.values()),'method':'direct falling-factor gamma reconstruction and finite-difference monomial-to-binomial conversion; no producer multiplication import','source_sha256':{f:hashlib.sha256((D/f).read_bytes()).hexdigest() for f in ['a4_polynomials.jsonl','core_corrections.jsonl']},'audit_code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(O/'template9_core_correction_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
