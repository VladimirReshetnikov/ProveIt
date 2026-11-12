#!/usr/bin/env python3
"""Pins, graph-cut wiring and exact free-ring controls, without Lean."""
from pathlib import Path
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items(): assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
proto=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
rows={row[0]:row[1:] for row in proto['source']}
expected={'E':['*','X','Y'],'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],
 'kY':['*','Y','k'],'c':['+','n_eta','kY'],'a':['+','E','Y'],
 'H':['+',3,'g15'],'Delta':['+','H','g17'],'b0':['+','X','g19'],
 'ell':['*','E','kY'],'g30':['+','ell','k'],'g40':['*','ell','g30'],
 'g41':['+',1,'g40'],'g42':['*','g39','g41'],'A0':['-','g38','g42'],
 'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g72':['-','g71','Q'],'V':['-','g76','c'],'Fa':['-','y2','g82'],
 'F0':['+',1,'A0'],'F1':['+',1,'A1'],'Fs':['+',1,'g72']}
for name,row in expected.items(): assert rows[name]==row,(name,rows.get(name))
# Independent sparse polynomial checks of the two nontrivial graph cuts.
N=10
class P:
 def __init__(self,t): self.t={m:c for m,c in t.items() if c}
 def __add__(self,o):
  o=lift(o); t=dict(self.t)
  for m,c in o.t.items(): t[m]=t.get(m,0)+c
  return P(t)
 __radd__=__add__
 def __neg__(self): return P({m:-c for m,c in self.t.items()})
 def __sub__(self,o): return self+-lift(o)
 def __rsub__(self,o): return lift(o)+-self
 def __mul__(self,o):
  o=lift(o); t={}
  for m,c in self.t.items():
   for n,d in o.t.items():
    k=tuple(x+y for x,y in zip(m,n)); t[k]=t.get(k,0)+c*d
  return P(t)
 __rmul__=__mul__
 def __eq__(self,o): return self.t==lift(o).t
def lift(n): return n if isinstance(n,P) else P({(0,)*N:n})
def var(i): return P({tuple(int(j==i) for j in range(N)):1})
kbase,R,U,gamma,X,a,c,H,E,Y=map(var,range(N)); k=kbase+1; m=E*Y; ell=E*(Y*k)
assert ell*(ell+k)==m*(m+1)*k*k
Dstar=U*(X+a*c)+H*(U*gamma-(kbase-R))
assert Dstar == (U*(X+a*c)+H*(U*gamma+R+1)) - H*k
source=(HERE/'EtaNaturalUnitNormAdapter.lean.src').read_text()
for x in ['def m (X Y : V) : V := X*Y*Y',
          'U q Y*(X+a X Y*c Y eta k)+H X Y*(U q Y*gamma+R+1)',
          'Residue90SignedNormsDraft.first_natural_norm',
          'Residue90SignedNormsDraft.main_pair_norm',
          'Residue90SignedNormsDraft.main_natural_norm',
          'EtaZeroEarlyCongruenceDraft.rank_congruence_of_main_norm',
          '(hq : 0<q) (hY : Y=q^3*s) (hY8 : 8≤Y) (hk : 0<k)']:
 assert x in source,x
print(json.dumps({'source_pins':pins,'literal_graph_rows_checked':len(expected),
 'first_and_main_cut_free_ring_identities':True,'lean_executed':False,
 'status':'conditional fact-level source; graph factor extraction and all provider proof obligations open'},sort_keys=True,indent=2))
