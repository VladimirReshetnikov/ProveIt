#!/usr/bin/env python3
"""Pins and exact graph-field polynomial checks; no Lean or artifact writes."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
g=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
assert len(g['witnesses'])==13 and g['fixed_numerals']==['beta','K0','MC','MF']
N=17
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
e={n:var(i) for i,n in enumerate(g['witnesses']+g['fixed_numerals'])}
for name,op,x,y in g['source']:
 a=L(x) if isinstance(x,int) else e[x];b=L(y) if isinstance(y,int) else e[y]
 e[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 if name=='ell':break
q=1+e['n_J']*e['beta'];Y=q*(q*q)*(e['n_s']+1);X=q*e['n_w'];k=e['n_eta']+e['n_zeta']+1
m=X*Y*Y;a=X*Y+Y;Delta=(3+4*a)+a*a;U=Y*q*q;c=e['n_eta']+Y*k
assert e['qm']==e['n_J']*e['beta'] and e['k']==k
assert e['ell']==m*k and e['U']==U and e['c']==c and e['Delta']==Delta
assert 1+(m*k)*(m*k+k)==1+m*(m+1)*k*k
s=(HERE/'EtaNaturalGraphNorms.lean.src').read_text()
for t in ['theorem field_b','theorem field_k','theorem field_ell','theorem field_U','theorem field_c','theorem field_delta','EtaNaturalUnitBridgeDraft.signed_norms','Residue90SignedNormsDraft.first_natural_norm','Residue90SignedNormsDraft.signed_norm_quotient','EtaNaturalJPositiveDraft.J_positive']:
 assert t in s,t
print(json.dumps({'source_pins':pins,'six_selected_fields_and_first_norm_identity':True,
 'lean_executed':False,'scope':'source-only graph-field checks; no all-model proof or provider authentication'},sort_keys=True,indent=2))
