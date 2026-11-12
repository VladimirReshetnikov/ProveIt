#!/usr/bin/env python3
"""Independent graph early-index source and finite binding review; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src':'6be2ab639c7b3b41eb81e52740dc54124a50fa35def7e62f5202a1d6e4bbe6d7',
'research/ordinary13-eta-natural-graph-early-index-model-draft/README.md':'e8c904d7e75f4ea9ddd58c58523b6085bbd0296fee3cd5a58aa696c60687c6ac',
'research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src':'b97bba84dc1aafe0dd8ee6eef287e003f6666f5e9ef645a74970f77bdbec1c61',
'research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src':'0832b087042375be828531a61d8baeca8676e64d386f6995e1f12de3bf441c41',
'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src':'6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src':'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src']
for t in ['theorem main_field','(hFq : v 1+1≤q p v)','EtaNaturalGapRankDraft.rank_representation p v hFq',
 'H p v*(U p v*v 12+rank p v+1)','def N (p : Fin 4 → ℕ)',
 'theorem main_pair_norm','EtaNaturalUnitBridgeDraft.signed_norms','Residue90SignedNormsDraft.main_pair_norm',
 'EtaNaturalGraphNormsDraft.first_natural_norm p v hz hbpos',
 'EtaNaturalRankIndexDraft.compact_early_index_of_norms K v tau hz htau\' hm\'',
 '⟨tau,n,w,htau\',hn,hnk,hnx,hny,hnmod,hnlow,hklow,hks⟩']:
 assert t in d,t
s0=s['research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src']
assert 'theorem compact_early_index_of_norms (K : ℕ) (v : Fin 13 → V) (tau : V)' in s0
assert 'let P:=U*(X p v+a*c)+H*(U*v 12+rank p v+1); let N:=H*k v' in s0
for t in ['xcoord n (2*(X p v*Y p v*Y p v-1)+1)=tau',
 '2*ycoord n (2*(X p v*Y p v*Y p v-1)+1)=k v',
 '(2*n)%((q p v)^4)=rank p v+1',
 'k v=2*n+4*(X p v*Y p v*Y p v)*w']:
 assert t in d and t in s0,t
assert 'theorem rank_representation' in s['research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src']
assert 'theorem signed_norms' in s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(901033);eta0=0
for j in range(300):
 e={n:rng.randrange(0,5) for n in g['witnesses']+g['fixed_numerals']}
 e['beta']=rng.randrange(6,12);e['n_J']=rng.randrange(1,4);e['n_F']=rng.randrange(0,3)
 if j%2==0:e['n_eta']=0
 eta0+=e['n_eta']==0
 for n,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 q=e['q'];F=e['F'];assert F<=q
 rank=((q-1)*(q-F)+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['n_J']
 assert e['R']==rank
 a=e['X']*e['Y']+e['Y'];H=3+4*a;U=e['Y']*q*q;c=e['n_eta']+e['Y']*e['k']
 P=U*(e['X']+a*c)+H*(U*e['n_gamma']+rank+1);N=H*e['k']
 assert e['Dstar']==P-N
 assert e['A1']==(P-N)**2-U*U*(1+(H+a*a)*c*c)
print(json.dumps({'source_sha256':pins,'prototype_rank_and_main_controls':300,'eta_zero_controls':eta0,'witness_slots_checked':True,'lean_executed':False,'scope':'source signatures and bounded graph controls; no Lean/model evaluation proof, exact index, port binding, zero map or iPRA theorem'},sort_keys=True,indent=2))
