#!/usr/bin/env python3
"""Independent pinned literal J=0 evaluation and finite sign controls."""
from pathlib import Path
import json,hashlib,itertools
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for name,digest in pins.items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
p=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
assert p['witnesses']==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma']
assert p['fixed_numerals']==['beta','K0','MC','MF']
# Sparse polynomial evaluation of the actual graph prefix after J=0.
N=16
class P:
 def __init__(self,t):self.t={m:c for m,c in t.items() if c}
 def __add__(self,o):
  o=L(o);d=dict(self.t)
  for m,c in o.t.items():d[m]=d.get(m,0)+c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.t.items()})
 def __sub__(self,o):return self+-L(o)
 def __rsub__(self,o):return L(o)+-self
 def __mul__(self,o):
  o=L(o);d={}
  for m,c in self.t.items():
   for n,e in o.t.items():
    k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
  return P(d)
 __rmul__=__mul__
 def __eq__(self,o):return self.t==L(o).t
def L(n):return n if isinstance(n,P) else P({(0,)*N:n})
def var(i):return P({tuple(int(j==i) for j in range(N)):1})
names=p['witnesses'][1:]+p['fixed_numerals']; assert len(names)==N
e={n:var(i) for i,n in enumerate(names)}; e['n_J']=L(0)
for name,op,a,b in p['source']:
 x=L(a) if isinstance(a,int) else e[a];y=L(b) if isinstance(b,int) else e[b]
 e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 if name=='Z':break
F=e['n_F']+1;alpha=e['n_alpha']+1;X=e['n_w'];K=e['K0']
assert e['qm']==0 and e['q']==1 and e['X']==X
assert e['Z']==F-(1-F-alpha)*(X+K)
count=0
for F,alpha,X,K in itertools.product(range(1,9),range(1,9),range(9),range(9)):
 C=1-F-alpha; z=F-C*(X+K)
 assert C<=0 and z>=F>0
 count+=1
assert 1-(1-1-1)*(0-1)==0
print(json.dumps({'source_pins':pins,'graph_prefix_J_zero_free_ring_identity':True,
 'model_natural_sign_controls':count,'negative_K0_first_norm_control':True,
 'lean_executed':False,'scope':'source-only audit; no graph proof elaboration or endpoint claim'},sort_keys=True,indent=2))
