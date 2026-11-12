#!/usr/bin/env python3
"""Independently pin source, graph rows, ring cuts and finite rank controls."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
r=ROOT/'research'
graphs=[json.loads((r/p).read_text()) for p in ['ordinary13-natural-unit-product88/candidate.json','ordinary13-natural-forced-gamma87/candidate.json','ordinary13-natural-forced-w86/candidate.json','ordinary13-eta-zero-graph-adapter-audit/prototype.json']]
assert [len(g['source']) for g in graphs]==[88,87,86,85]
for a,b,n,v in zip(graphs,graphs[1:],['gamma','w','eta'],['n_gamma','n_w','n_eta']):
 assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
 assert [[v if x==n else x for x in row] for row in a['source'] if row!=[n,'+',v,1]]==b['source']
rows={row[0]:row[1:] for row in graphs[-1]['source']}
for n,row in {'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],
 'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59']}.items():assert rows[n]==row
# Sparse ring proof that the actual Dstar is P−N with rank R (not R+XYq).
N=8
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
U,X,a,c,H,R,kbase,gamma=map(var,range(N)); k=kbase+1
D=U*(X+a*c)+H*(U*gamma-(kbase-R));Pn=U*(X+a*c)+H*(U*gamma+R+1)
assert D==Pn-H*k
# Check stronger enlarged-rank arithmetic, including the weaker actual-R gap.
count=0
for q,X,s,eta,zeta in itertools.product(range(2,9),range(1,5),range(1,4),range(0,4),range(1,4)):
 Y=q**3*s;m=X*Y*Y;R=q**4-q**3-q-1;k=8*m+4
 assert q<=Y and q**4<=m and X<=m
 assert R+1<=q**4 and m<k and R+1<k
 assert k<=Y*k and X<eta+Y*k
 count+=1
direct=(r/'ordinary13-gamma87-to88-model-draft/GammaDirectRankGap.lean.src').read_text()
facts=(r/'ordinary13-gamma87-to88-model-draft/GammaNoExtraFacts.lean.src').read_text()
assert 'GammaDirectRankGapDraft.direct_rank_gap' in facts and 'Residue90GammaModelDraft.enlarged_rank_gap' not in facts
assert 'theorem direct_rank_gap' in direct and 'omega' not in direct.split('theorem direct_rank_gap',1)[1] and 'nlinarith' not in direct.split('theorem direct_rank_gap',1)[1]
s=(r/'ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src').read_text()
assert 'W86To87TransportDraft.zero_iff' in s and 'EtaUnshift85TransportDraft.zero_iff' in s
part=s.split('theorem gamma_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
assert 'ForcedEta' not in part and 'raiseW v' in part and 'raiseEta w' in part
assert '(h88 : PolynomialBridge (GammaShifted88GraphDraft.literal' in s
print(json.dumps({'source_pins':pins,'exact_gamma_w_eta_row_substitutions':True,
 'no_extra_main_carrier_ring_identity':True,'rank_inequality_controls':count,
 'lean_executed':False,'scope':'source and finite arithmetic audit only; no model/provider or endpoint proof'},sort_keys=True,indent=2))
