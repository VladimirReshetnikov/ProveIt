#!/usr/bin/env python3
"""Exact residual congruences and finite lift controls; no all-model proof."""
import hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;old=json.loads((P.parent/'nine-sharing-sign27-sextic-normalized-root-candidate/seed.json').read_text());new=json.loads((P/'seed.json').read_text())
# Sparse formal multivariate integer polynomials; atoms are new coordinates and symbolic ports.
def C(c):return {():c} if c else {}
def atom(x):return {((x,1),):1}
def add(a,b,s=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+s*v
 return {k:v for k,v in r.items() if v}
def mul(a,b):
 r={}
 for x,v in a.items():
  for y,w in b.items():
   d=dict(x)
   for k,e in y:d[k]=d.get(k,0)+e
   z=tuple(sorted(d.items()));r[z]=r.get(z,0)+v*w
 return {k:v for k,v in r.items() if v}
V={i:atom('v'+str(i)) for i in range(27)};ports={k:atom(k) for k in ('beta','K0','MC','MF')};one=C(1);a=mul(ports['beta'],add(V[1],one));q=add(a,one);n=add(V[2],one);t=add(V[3],one);g=add(add(mul(a,q),t),mul(a,n),-1);H=add(ports['K0'],add(V[9],one));f=add(V[4],one)
def poly(tree,old_side=False):
 op=tree[0]
 if op=='num':return C(tree[1])
 if op=='port':return ports[tree[1]]
 if op=='var':
  i=tree[1]
  if old_side and i==22:return g
  return V[i-(old_side and i>22)]
 x,y=poly(tree[1],old_side),poly(tree[2],old_side)
 return mul(x,y) if op=='mul' else add(x,y,1 if op=='add' else -1)
oldrows={r['gate']:r for r in old['residuals']};newrows={r['gate']:r for r in new['residuals']};assert len(oldrows)==18 and len(newrows)==17 and set(oldrows)-{'gap'}==set(newrows)
q3=poly(newrows['q3']['expr']);delta=mul(add(a,n,-1),q3);changed=[]
for gate in newrows:
 diff=add(poly(oldrows[gate]['expr'],True),poly(newrows[gate]['expr']),-1)
 if gate in ('tau','cTminusR'):assert diff=={k:-v for k,v in delta.items()};changed.append(gate)
 else:assert not diff
assert poly(oldrows['gap']['expr'],True)=={}
nt=poly(newrows['Nt']['expr']);ntform=add(add(mul(H,add(add(q,n,-1),t,-1)),n,-1),mul(add(f,one,-1),a),-1);assert nt==ntform
# Congruence exact for all integer valuations; it becomes equality when q3=0.
def degree(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 x,y=degree(t[1]),degree(t[2]);return x+y if t[0]=='mul' else max(x,y)
assert max(degree(r['expr']) for r in new['residuals'])==3 and oldrows['q3']==newrows['q3'] and new['witness_count']==26
# Evaluate finite lifts with q3=0 and nonnegative reconstructed gap (v2=0); these are controls only.
def ev(t,v,p):
 op=t[0]
 if op=='num':return t[1]
 if op=='port':return p[t[1]]
 if op=='var':return v[t[1]]
 x,y=ev(t[1],v,p),ev(t[2],v,p);return x+y if op=='add' else x-y if op=='sub' else x*y
rng=random.Random(26022);p={'beta':3,'K0':7,'MC':5,'MF':9}
for _ in range(16):
 v=[rng.randrange(4) for _ in range(27)];v[2]=0;aa=p['beta']*(v[1]+1);qq=aa+1;v[15]=qq**3;gg=aa*(qq-(v[2]+1))+(v[3]+1);assert gg>=0;w=v[:22]+[gg]+v[22:];assert len(w)==28
 before={r['gate']:ev(r['expr'],w,p) for r in old['residuals']};after={r['gate']:ev(r['expr'],v,p) for r in new['residuals']};assert before.pop('gap')==0 and before==after
print(json.dumps({'status':'PASS_EXACT_POLYNOMIAL_CONGRUENCE_AND_FINITE_CONTROLS','seed_sha256':hashlib.sha256((P/'seed.json').read_bytes()).hexdigest(),'witnesses':26,'residuals':17,'max_residual_syntactic_degree':3,'modified_residuals':changed,'difference':'old(lift)-new = -(a-n)*q3 for tau and cTminusR, zero for all other surviving rows','Nt_identity':'Nt=H*(q-n-t)-n-(f-1)*a','finite_lift_controls':16,'scope':'formal polynomial identities and finite controls only; model positivity, zero equivalence and endpoint unproved'},indent=2,sort_keys=True))
