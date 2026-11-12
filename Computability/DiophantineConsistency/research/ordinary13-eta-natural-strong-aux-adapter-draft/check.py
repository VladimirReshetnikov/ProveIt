#!/usr/bin/env python3
"""Source pins and exact selected algebra; does not run Lean."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
g=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
rows={r[0]:r[1:] for r in g['source']}
for name,row in {'i':['+','n_i',1],'T':['+','n_T',1],
 'c':['+','n_eta','kY'],'c2':['*','c','c'],'g17':['*','a','a'],
 'Delta':['+','H','g17'],'f2':['*','n_f','n_f'],'rho':['-','f2',1],
 'Q':['*','Delta','rho'],'I':['*','c2','i'],'g71':['*','I','I'],
 'g72':['-','g71','Q'],'g74':['*','T','c'],'g75':['-','g74','R'],
 'g76':['*','f2','g75'],'V':['-','g76','c'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82']}.items():assert rows[name]==row,(name,rows.get(name))
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
strong=I*I-Q
nat_strong=(i*c*c)*(i*c*c)+D-D*f*f
assert strong==nat_strong
assert z+c==f*f*(T*c-R)
A=f*f*(T*c);B=f*f*R+c
assert z==A-B
aux=y*y-Q*(y*y-z*z)-1
balance=Q*z*z+y*y-1-Q*y*y
assert aux==balance
s=(HERE/'EtaNaturalStrongAux.lean.src').read_text()
for x in ['theorem ordinary_strong_of_signed','theorem f_positive_of_strong',
 'theorem strict_bounds_of_strong','AuxOffsetFactsDraft.aux_strict_bounds',
 'theorem index_aux_of_direct','AuxOffsetFactsDraft.positive_offset_of_direct',
 'P72Root.ι_tsub hf1','P72Root.ι_magnitude_sq','linear_combination -hsR']:
 assert x in s,x
print(json.dumps({'source_pins':pins,'graph_rows_checked':19,
 'strong_ordinate_auxiliary_free_ring_identities':True,
 'lean_executed':False,'status':'fact-level conditional source; all graph and model obligations remain open'},sort_keys=True,indent=2))
