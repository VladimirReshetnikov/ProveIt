#!/usr/bin/env python3
"""Independent graph-to-strong/aux interface checks; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src':'25587629cbab4bc8a53a49ed9244362d04d8fb79ac6ab675dcfa429f83dd3dc2',
'research/ordinary13-eta-natural-graph-strong-aux-model-draft/README.md':'ba638d99b23fe953034ebac3c9e1bced95c1394e9c5369eb7910b9c71e302126',
'research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src':'c13a8d83acb13784027eb63dde7f61d0c4bd7f07b0f64e95afbf0eb9950e0abd',
'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src':'6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863',
'research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src':'b97bba84dc1aafe0dd8ee6eef287e003f6666f5e9ef645a74970f77bdbec1c61',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src':'8b53f77e8f9bb8b374f91aee18700a6143e8f41fa5332ea8f65ca503d70e69cd'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src']
for t in ['theorem field_f','theorem field_y','theorem field_I','theorem field_ordinate',
 '(hFq : v 1+1≤q p v)','EtaNaturalGapRankDraft.rank_representation p v hFq',
 'theorem ordinary_strong','⟨_,_,hs,_⟩','theorem direct_auxiliary','⟨_,_,_,ha⟩',
 'theorem index_hypotheses_of_geometry','EtaNaturalStrongAuxDraft.strict_bounds_of_strong',
 'EtaNaturalStrongAuxDraft.index_aux_of_direct']:
 assert t in d,t
v=s['research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src']
for t in ['(heta : v 9=0)','(hstrong : let p:=','(haux : let p:=','let c:=Y p v*k v',
 '(ι (c*c*(v 4+1)):DiffRing V)','ι (v 3*v 3*((v 5+1)*c))-ι (v 3*v 3*rank p v+c)']:
 assert t in v,t
u=s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
assert 'I*I=Delta*(f*f-1)' in u and 'y*y-Delta*(f*f-1)*(y*y-vv*vv)=1' in u
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(620185);eta0=0
for j in range(300):
 e={n:rng.randrange(0,5) for n in g['witnesses']+g['fixed_numerals']}
 e['beta']=rng.randrange(6,12);e['n_J']=rng.randrange(1,5);e['n_F']=rng.randrange(0,3)
 if j%2==0:e['n_eta']=0
 eta0+=e['n_eta']==0
 for n,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 q=e['q'];F=e['F'];assert F<=q
 rank=((q-1)*(q-F)+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['n_J']
 assert e['R']==rank
 f=e['n_f'];c=e['c'];T=e['n_T']+1;i=e['n_i']+1;y=e['n_y'];D=e['Delta']
 z=f*f*T*c-(f*f*rank+c)
 assert e['V']==z and e['I']==c*c*i and e['g72']==e['I']**2-D*(f*f-1)
 assert e['Fa']==y*y-D*(f*f-1)*(y*y-z*z)
 if e['n_eta']==0:assert c==e['Y']*e['k']
print(json.dumps({'source_sha256':pins,'graph_strong_aux_controls':300,'eta_zero_controls':eta0,'lean_executed':False,'scope':'source interfaces and bounded graph controls only; no Lean, all-model field casts, graph forcing, zero maps or iPRA endpoint'},sort_keys=True,indent=2))
