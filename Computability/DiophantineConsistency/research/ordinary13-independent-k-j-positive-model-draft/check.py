from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-j-positive-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
u=Path('research/ordinary13-independent-k-unit-norm-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(u/'check.py')])==(u/'receipt.json').read_bytes()
old=Path('research/ordinary13-eta-zeta-zero-graph-obstruction-draft/EtaZetaNaturalJPositive.lean.src').read_text()
expected=(old.replace('import EtaZetaNaturalUnitBridge','import IndependentKUnitBridge').replace('EtaZetaNaturalJPositiveDraft','IndependentKJPositiveDraft').replace('EtaZetaNaturalUnitBridgeDraft','IndependentKUnitBridgeDraft').replace('EtaZetaNaturalUnitGraphDraft','IndependentKUnitGraphDraft').replace('exact generated\neta/zeta-natural prototype','exact generated\nindependent-k child candidate').replace('actual prototype has q=1','actual child has q=1').replace('eta, X, or zeta assumption','eta, X, or k assumption'))
s=(D/'IndependentKJPositive.lean.src').read_text();assert s==expected
assert '(p : Fin 4 → ℕ) (v : Fin 13 → V)' in s
assert 'IndependentKUnitBridgeDraft.signed_norms pp v hz' in s
assert 'ι (v 6)+ι (p 1:V)' in s
# Sparse multivariate polynomial evaluation of actual graph through Z at J=0.
G=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());N=17;zero=(0,)*N
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    t=tuple(a+b for a,b in zip(k,j));r[t]=r.get(t,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({zero:x})
def var(i):
 x=[0]*N;x[i]=1;return P({tuple(x):1})
a={name:var(i) for i,name in enumerate(G['witnesses'])};a['n_J']=pol(0)
a.update({name:var(i+13) for i,name in enumerate(G['fixed_numerals'])})
for name,op,l,r in G['source']:
 x=a[l] if isinstance(l,str) else pol(l);y=a[r] if isinstance(r,str) else pol(r)
 a[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 if name=='Z':break
F=a['n_F']+1;alpha=a['n_alpha']+1;X=a['n_w'];K=a['K0']
assert a['qm']==0 and a['q']==1 and a['X']==X
assert a['Z']==F-(1-F-alpha)*(X+K)
# Distinct witnesses exercise unrestricted child k and eta, and natural K.
rng=random.Random(52704)
for _ in range(500):
 w=[rng.randrange(15) for i in range(13)];w[0]=0;p=[rng.randrange(15) for i in range(4)]
 d=dict(zip(G['witnesses'],w));d.update(zip(G['fixed_numerals'],p))
 for n,op,l,r in G['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  if n=='A0':break
 F=w[1]+1;alpha=w[2]+1;Z=F-(1-F-alpha)*(w[6]+p[1])
 assert d['Z']==Z and Z>0 and d['A0']==Z*Z>0
print(json.dumps({'child_unit_receipt_reproduced':True,'exact_parent_source_adaptation':True,'actual_child_J0_root_polynomial_identity':True,'actual_child_J0_positive_controls':500,'nat_tuple_assumptions':'all four ports natural; no strict beta bound; K natural','lean_executed':False,'proof_or_provider_replayed':False},sort_keys=True,indent=2))
