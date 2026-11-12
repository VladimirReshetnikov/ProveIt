#!/usr/bin/env python3
"""Pinned graph and signed strong/auxiliary ring checks; never runs Lean."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
g=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
assert g['witnesses'][3:6]==['n_f','n_i','n_T'] and g['witnesses'][11]=='n_y'
r={row[0]:row[1:] for row in g['source']}
expected={'i':['+','n_i',1],'T':['+','n_T',1],
 'c':['+','n_eta','kY'],'c2':['*','c','c'],'Delta':['+','H','g17'],
 'f2':['*','n_f','n_f'],'rho':['-','f2',1],'Q':['*','Delta','rho'],
 'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],
 'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],
 'V':['-','g76','c'],'y2':['*','n_y','n_y'],'V2':['*','V','V'],
 'g81':['-','y2','V2'],'g82':['*','Q','g81'],'Fa':['-','y2','g82']}
for n,row in expected.items():assert r[n]==row,(n,r.get(n))
# Check the graph cut and target equations as free commutative polynomials.
N=7
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
c,i,D,f,T,R,y=map(var,range(N));I=c*c*i;Q=D*(f*f-1);z=f*f*(T*c-R)-c
assert I*I-Q==(i*c*c)*(i*c*c)+D-D*f*f
assert z==f*f*(T*c)-(f*f*R+c)
aux=y*y-Q*(y*y-z*z)-1
assert aux==Q*z*z+y*y-1-Q*y*y
s=(HERE/'EtaNaturalGraphStrongAux.lean.src').read_text()
for x in ['theorem field_f','theorem field_y','theorem field_I','theorem field_ordinate',
 'EtaNaturalGapRankDraft.rank_representation p v hFq',
 'EtaNaturalUnitBridgeDraft.signed_norms','EtaNaturalStrongAuxDraft.ordinary_strong_of_signed',
 'EtaNaturalStrongAuxDraft.strict_bounds_of_strong','EtaNaturalStrongAuxDraft.index_aux_of_direct',
 '(hc : 1<c p v)','(hdelta : 0<EtaNaturalGraphNormsDraft.delta p v)','(hsmall :']:
 assert x in s,x
print(json.dumps({'source_pins':pins,'prototype_rows_checked':len(expected),
 'strong_ordinate_auxiliary_free_ring_identities':True,'lean_executed':False,
 'scope':'conditional source only; no graph/provider build or endpoint'},sort_keys=True,indent=2))
