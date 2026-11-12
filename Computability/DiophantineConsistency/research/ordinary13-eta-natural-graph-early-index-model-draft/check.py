#!/usr/bin/env python3
"""Pinned graph cut and exact polynomial identities; no Lean execution."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for name,digest in pins.items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
p=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
rows={r[0]:r[1:] for r in p['source']}
expected={'q':['+',1,'qm'],'qF':['-','q','F'],'G':['+','alpha','g44'],
 'g44':['*','qF','qm'],'g46':['-','q2',1],'g47':['*','G','g46'],
 'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],
 'R':['+','g47','g50'],'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],
 'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59']}
for n,r in expected.items():assert rows[n]==r,(n,rows.get(n))
N=13
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
b,F,alpha,J,MC,MF,kbase,U,X,a,c,H,gamma=map(var,range(N))
q=1+b; R=(alpha+(q-F)*b)*(q*q-1)+J*(MC+MF*q);k=kbase+1
Rnatural=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
assert R==Rnatural
D=U*(X+a*c)+H*(U*gamma-(kbase-R))
Pn=U*(X+a*c)+H*(U*gamma+R+1);Nn=H*k
assert D==Pn-Nn
count=0
for q,F,a,J,MC,MF in itertools.product(range(1,8),range(1,8),range(1,4),range(3),range(3),range(3)):
 if F>q:continue
 b=q-1
 r=(a+(q-F)*b)*(q*q-1)+J*(MC+MF*q)
 rn=((q-1)*(q-F)+a)*(q*q-1)+(MC+q*MF)*J
 assert r==rn;count+=1
s=(HERE/'EtaNaturalGraphEarlyIndex.lean.src').read_text()
for x in ['EtaNaturalGapRankDraft.rank_representation','EtaNaturalUnitBridgeDraft.signed_norms',
 'Residue90SignedNormsDraft.main_pair_norm','EtaNaturalGraphNormsDraft.first_natural_norm',
 'EtaNaturalRankIndexDraft.compact_early_index_of_norms','hgap','hFq','⟨tau,n,w,htau\'']:
 assert x in s,x
print(json.dumps({'source_pins':pins,'checked_graph_rows':len(expected),
 'signed_main_and_rank_ring_identities':True,'bounded_natural_rank_controls':count,
 'lean_executed':False,'scope':'source-only early congruence; no compiled provider, exact index, zero map or endpoint'},sort_keys=True,indent=2))
