#!/usr/bin/env python3
"""Independent boundary source-interface and finite arithmetic checks; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalParityBoundary.lean.src':'4d308543932fcdf46767f3d58e8324f653438d72adccdae24addb16b149236ab',
'research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src':'8b53f77e8f9bb8b374f91aee18700a6143e8f41fa5332ea8f65ca503d70e69cd',
'research/ordinary13-eta-natural-parity-boundary-draft/README.md':'8621ffbeb7da207861b66ab0e098ca62fb32dde3d53cad223782ef630a82190a',
'research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src':'6be2ab639c7b3b41eb81e52740dc54124a50fa35def7e62f5202a1d6e4bbe6d7',
'research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src':'b97bba84dc1aafe0dd8ee6eef287e003f6666f5e9ef645a74970f77bdbec1c61',
'research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src':'0832b087042375be828531a61d8baeca8676e64d386f6995e1f12de3bf441c41',
'research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src':'c13a8d83acb13784027eb63dde7f61d0c4bd7f07b0f64e95afbf0eb9950e0abd',
'research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src':'aac1707680c5894a8dde85b63fba8b4c1417f8e7296022a2c686ac3928caaa06',
'research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src':'5ccefb9efd90dad307ffcf55d67597b32a620d02e0a8b09eb88e642474a12782',
'research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src':'a5aac5250b0b4c05fa765ed1013e5287706f038ea60e5083d9c4cba4025e0e74',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
a=s['research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalParityBoundary.lean.src']
b=s['research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src']
for t in ['(hq3 : 3≤q) (hX : 0<X) (hs : 0<s0)', '(hk : 0<k) (hi : 0<i) (hR26 : 26≤R)',
 'EtaNaturalNormLargeKDraft.large_first_ordinate X Y 0 k tau D g',
 'AuxGeometryEtaNaturalDraft.geometry_of_large_k X Y 0 k D hYpos hlarge\' hD',
 'EtaNaturalStrongAuxDraft.ordinary_strong_of_signed c i D f hstrong',
 'EtaNaturalStrongAuxDraft.index_aux_of_direct c D f T R y',
 'ArithmeticPellClassification.solution_index a g c hg',
 'EtaZeroIndexParityDraft.eta_zero_contradiction q X Y k R g c a s0 i f T u n w (q^4) m']:
 assert t in a,t
for t in ['(heta : v 9=0)','(hstrong : let p:=','(haux : let p:=',
 'EtaNaturalGraphNormsDraft.natural_norms_of_graph p v hz hbeta',
 '⟨_,g,hg⟩','⟨tau,n,w,hfirst,_,_,_,hny,hnmod,_,_,hks⟩',
 'EtaNaturalGraphEarlyIndexDraft.compact_early_index K v hz',
 '(k v) (rank p v) tau g (v 4+1) (v 3) (v 5+1) (v 11) n w (v 7+1)',
 'hR26 hfirst hmain hny hks hRmu hnmod hstrong haux']:
 assert t in b,t
large=s['research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src']
assert 'theorem large_first_ordinate (X Y eta zeta tau Delta d : V)' in large
assert '(hX : 0<X) (hY : 0<Y) (hzeta : 0<zeta)' in large
geo=s['research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src']
assert 'theorem geometry_of_large_k (X Y eta k Delta : V) (hY : 0<Y)' in geo
assert '(heta : 0<eta)' not in geo
assert '∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y' in s['Lean/DiophantineConsistency/ArithmeticPellClassification.lean']
idx=s['research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src']
assert 'theorem eta_zero_contradiction (q X Y k R g c a y0 i\' f T u n s μ m : V)' in idx
geom=0
for X in range(1,11):
 for Y in range(1,11):
  for offset in range(12):
   k=8*X*Y*Y+4+offset;A=X*Y+Y+2;c=Y*k;D=A*A-1
   assert A<c and 1<c and 0<D<c**3
   geom+=1
parity=0
for a0 in range(16):
 x,y=1,0
 for n in range(40):
  assert y%2==n%2
  x,y=((a0+2)*x+(a0+1)*(a0+3)*y)%2,(x+(a0+2)*y)%2
  parity+=1
G=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(640274)
for _ in range(200):
 e={name:rng.randrange(0,5) for name in G['witnesses']+G['fixed_numerals']}
 e['n_eta']=0;e['n_J']=rng.randrange(1,5);e['beta']=rng.randrange(6,11);e['n_F']=rng.randrange(0,3)
 for name,op,l,r in G['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 assert e['F']<=e['q'];q=e['q'];rank=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['n_J']
 c=e['Y']*e['k'];A=e['X']*e['Y']+e['Y'];D=3+4*A+A*A
 z=e['n_f']**2*(e['T']*c)-(e['n_f']**2*rank+c)
 assert rank==e['R'] and c==e['c'] and D==e['Delta'] and z==e['V']
 assert e['g72']==(c*c*e['i'])**2-D*(e['n_f']**2-1)
 assert e['Fa']==e['n_y']**2-D*(e['n_f']**2-1)*(e['n_y']**2-z*z)
print(json.dumps({'source_sha256':pins,'geometry_controls':geom,'pell_parity_controls':parity,'eta_zero_binding_controls':200,'lean_executed':False,'scope':'bounded arithmetic/source-interface review only; no all-model proof, graph factor binding, zero map, or iPRA endpoint'},sort_keys=True,indent=2))
