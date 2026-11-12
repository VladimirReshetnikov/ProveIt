#!/usr/bin/env python3
"""Independent parity-composition source/interface and finite graph review."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-graph-parity-composition-draft/EtaNaturalGraphParity.lean.src':'1a5a20a6b87f7521fa27fb8f7aded46b2b8183ec09c22679b857740522b12245',
'research/ordinary13-eta-natural-graph-parity-composition-draft/README.md':'10eac9ec286c6c4e533f35da480bf1be22d7abfd3cc0502c5c0ab06aaa568817',
'research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src':'25587629cbab4bc8a53a49ed9244362d04d8fb79ac6ab675dcfa429f83dd3dc2',
'research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src':'8b53f77e8f9bb8b374f91aee18700a6143e8f41fa5332ea8f65ca503d70e69cd',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src':'6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863',
'research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src':'b97bba84dc1aafe0dd8ee6eef287e003f6666f5e9ef645a74970f77bdbec1c61',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-graph-parity-composition-draft/EtaNaturalGraphParity.lean.src']
t=s['research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalCompactParity.lean.src']
def binder(src,name):
 start=src.index('('+name+' :');depth=0
 for i in range(start,len(src)):
  if src[i]=='(':depth+=1
  elif src[i]==')':
   depth-=1
   if depth==0:return src[start+len(name)+3:i]
 raise AssertionError(name)
def local_type(src,name):
 start=src.index('have '+name+' :')+len('have '+name+' :')
 end=src.index(':= by',start)
 return src[start:end]
def norm(x):return ''.join(x.split())
for name in ('hstrong','haux'):
 local=local_type(d,name)
 formal=binder(t,name)
 assert 'let a:=' in formal and 'let a:=' in local
 assert norm(formal[formal.index('let a:='):])==norm(local[local.index('let a:='):]),name
for t0 in ['theorem eta_zero_impossible','(heta : v 9=0)',
 'EtaNaturalJPositiveDraft.J_positive p v hz','EtaNaturalGapRankDraft.gap p v hz hbeta',
 '⟨_,_,hs,_⟩','EtaNaturalGraphStrongAuxDraft.field_I','EtaNaturalGraphNormsDraft.field_delta',
 'EtaNaturalGraphStrongAuxDraft.field_f','EtaNaturalGraphStrongAuxDraft.direct_auxiliary p v hz hFq',
 'EtaNaturalCompactParityDraft.eta_zero_of_represented_factors K v hz heta hstrong haux',
 'theorem eta_positive','le_antisymm (le_of_not_gt hn) (Arithmetic.zero_le _)']:
 assert t0 in d,t0
head=d.split('theorem eta_zero_impossible',1)[1].split(':= by',1)[0]
assert '(hstrong :' not in head and '(haux :' not in head
f=s['research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src']
assert 'theorem field_I' in f and 'theorem field_f' in f and 'theorem direct_auxiliary' in f
assert '(hFq : v 1+1≤q p v)' in f
u=s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
assert 'I*I=Delta*(f*f-1)' in u and 'y*y-Delta*(f*f-1)*(y*y-vv*vv)=1' in u
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(471082)
for j in range(250):
 e={name:rng.randrange(0,5) for name in g['witnesses']+g['fixed_numerals']}
 e['n_eta']=0;e['n_J']=rng.randrange(1,5);e['beta']=rng.randrange(6,12);e['n_F']=rng.randrange(0,3)
 for name,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 assert e['F']<=e['q']
 q=e['q'];rank=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['n_J']
 c=e['Y']*e['k'];a=e['X']*e['Y']+e['Y'];D=3+4*a+a*a;f=e['n_f'];T=e['n_T']+1;y=e['n_y'];i=e['n_i']+1
 z=f*f*T*c-(f*f*rank+c)
 assert e['R']==rank and e['c']==c and e['Delta']==D and e['I']==c*c*i and e['V']==z
 assert e['g72']==(c*c*i)**2-D*(f*f-1)
 assert e['Fa']==y*y-D*(f*f-1)*(y*y-z*z)
print(json.dumps({'source_sha256':pins,'boundary_strong_aux_types_exact_after_let_p':True,'eta_zero_graph_controls':250,'lean_executed':False,'scope':'source and finite graph checks; no Lean, all-model forcing, zero-map proof, provider build or iPRA endpoint'},sort_keys=True,indent=2))
