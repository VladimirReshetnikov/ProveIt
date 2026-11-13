from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-eta-natural-parity-boundary-draft')
fs=[p/'EtaNaturalParityBoundary.lean.src',p/'EtaNaturalCompactParity.lean.src',p/'README.md',
Path('research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src'),
Path('research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src'),
Path('research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src'),
Path('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src'),
Path('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),
Path('research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src'),
Path('research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['contradiction_of_facts','(hfirst :','(hmain :','(hny :','(hks :','(hRmu :','(hnmod :',
 '(hstrong :','(haux :','EtaNaturalNormLargeKDraft.large_first_ordinate',
 'AuxGeometryEtaNaturalDraft.geometry_of_large_k','EtaNaturalStrongAuxDraft.strict_bounds_of_strong',
 'EtaNaturalStrongAuxDraft.index_aux_of_direct','ArithmeticPellClassification.solution_index',
 'EtaZeroIndexParityDraft.eta_zero_contradiction']:
 assert x in s[0],x
for x in ['eta_zero_of_represented_factors','(heta : v 9=0)','(hstrong :','(haux :',
 'EtaNaturalGraphEarlyIndexDraft.compact_early_index','EtaNaturalGraphNormsDraft.natural_norms_of_graph',
 'EtaNaturalRankIndexDraft.compact_rank_at_least_26','EtaNaturalGapRankDraft.compact_rank_window']:
 assert x in s[1],x
assert '(hmainPair :' not in s[1]
for a in range(12):
 x,y=1,0
 for t in range(24):
  assert y%2==t%2
  x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
G=json.loads(s[10]);rng=random.Random(1916);count=0
for _ in range(500):
 v={key:rng.randrange(0,5) for key in G['witnesses']+G['fixed_numerals']};v['n_eta']=0
 e=v.copy()
 for name,op,l,r in G['source']:
  x=l if isinstance(l,int) else e[l];y=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 if e['q']<e['F']:continue
 q=e['q'];R=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*v['n_J']
 assert e['R']==R
 c=e['Y']*e['k'];D=3+4*e['a']+e['a']**2
 z=v['n_f']**2*((v['n_T']+1)*c)-(v['n_f']**2*R+c)
 assert e['V']==z and e['g72']==(c*c*(v['n_i']+1))**2-D*(v['n_f']**2-1)
 assert e['Fa']==v['n_y']**2-D*(v['n_f']**2-1)*(v['n_y']**2-z*z)
 count+=1
assert count>100
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'pell_parity_controls':288,'eta_zero_represented_factor_controls':count,'lean_executed':False,
 'status':'unelaborated; graph strong/aux representation and all provider obligations open'},sort_keys=True,indent=2))
