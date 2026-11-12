#!/usr/bin/env python3
"""Independent gap/rank source and bounded arithmetic review; no Lean."""
from pathlib import Path
import hashlib,itertools,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src':'6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863',
'research/ordinary13-eta-natural-gap-rank-model-draft/README.md':'17bb7216de924baa3801aba9ad5c92cb0a48d67f89765168bf1642d23d250014',
'research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src':'e3bace196b09c86927bd178c279111ab4c97d076a18711c676ff127f002fe063',
'research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src':'c30a9d4fe05ca8878e7681f1987b27e51af5db5bc4366d65b8cf050589636c63',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src':'11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a',
'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src':'422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805',
'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
'Lean/DiophantineConsistency/Compact44/CompactConcreteIncrement.lean':'7e189dd000c9c6211752146562d4fdcd353f6ef5c48fb1522cde9c2b070bbd0d'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src']
for t in ['theorem first_norm','theorem gap_of_J','(hJ : 0<v 0) (hbeta : 0<(p 0:V))',
 'ι (m p v*k v)+ι (k v)+ι (v 8)-ι (k v)*Bt p v',
 'have hk1 : 1≤k v','have hr : (0:DiffRing V)≤ι (v 8)',
 'theorem rank_representation','(hFq : v 1+1≤q p v)',
 'Residue90GraphNormsDraft.rank_representation','theorem compact_rank_window',
 'CompactFixedBeta.bounds','Residue90CompactPortBoundsDraft.compact_rank_window']:
 assert t in d,t
assert 'theorem signed_norms' in s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
assert 'theorem rank_representation (p : Fin 4 → ℕ)' in s['research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s['Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in s['Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean']
assert 'def mask : V := (Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ)' in s['Lean/DiophantineConsistency/Compact44/CompactConcreteIncrement.lean']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rows={r[0]:r for r in g['source']}
for row in [['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],['g31','+','g30','n_r'],['Bt','-','g27','F'],['Z','-','g32','Bt']]:assert rows[row[0]]==row
# Exact symbolic cut identities using coefficient arithmetic over Z[m,k,b,r,B].
N=5
class P:
 def __init__(self,t):self.t={k:v for k,v in t.items() if v}
 def __add__(self,o):
  o=up(o);d=self.t.copy()
  for k,v in o.t.items():d[k]=d.get(k,0)+v
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.t.items()})
 def __sub__(self,o):return self+-up(o)
 def __rsub__(self,o):return up(o)+-self
 def __mul__(self,o):
  o=up(o);d={}
  for a,v in self.t.items():
   for b,w in o.t.items():
    k=tuple(x+y for x,y in zip(a,b));d[k]=d.get(k,0)+v*w
  return P(d)
 __rmul__=__mul__
 def __eq__(self,o):return self.t==up(o).t
def up(x):return x if isinstance(x,P) else P({(0,)*N:x})
def var(i):return P({tuple(int(i==j) for j in range(N)):1})
m,k,b,r,B=map(var,range(N));ell=m*k;Z=b*(ell+k+r-k*B)-B
assert (ell+k)*(ell+k)-(1+m*(m+1)*k*k)==ell*k+k*k-1
assert Z-b*(ell+k)==b*(r-k*B)-B
bounds=boundary=0
for b,m,k,r,F,alpha,X,K in itertools.product(range(1,5),range(4),range(1,5),range(3),range(1,4),range(1,4),range(3),range(2)):
 q=1+b;C=q-F-alpha
 if C>0:continue
 B=C*(X+K)-F;ell=m*k;Z=b*(ell+k+r-k*B)-B
 assert B<0 and Z>b*(ell+k)>=0 and (ell+k)**2>=1+m*(m+1)*k*k
 assert Z*Z>b*b*(1+m*(m+1)*k*k)
 bounds+=1;boundary+=k==1 and r==0
assert boundary>0
rng=random.Random(53012);graph=rank=0
for _ in range(300):
 e={n:rng.randrange(0,6) for n in g['witnesses']+g['fixed_numerals']}
 for n,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 m=e['X']*e['Y']**2;k=e['k'];B=(e['q']-e['F']-e['alpha'])*(e['X']+e['K0'])-e['F']
 assert e['Z']==e['qm']*(m*k+k+e['n_r']-k*B)-B
 assert e['A0']==e['Z']**2-e['qm']**2*(1+m*(m+1)*k*k);graph+=1
 if e['q']>=e['F']:
  R=((e['q']-1)*(e['q']-e['F'])+e['alpha'])*(e['q']**2-1)+(e['MC']+e['q']*e['MF'])*e['n_J']
  assert e['R']==R;rank+=1
assert rank>0
print(json.dumps({'source_sha256':pins,'exact_polynomial_identities':2,'gap_controls':bounds,'k1_r0_controls':boundary,'prototype_controls':graph,'rank_cast_toy_controls':rank,'lean_executed':False,'scope':'source interfaces, exact polynomial cuts and finite controls; no Lean/model graph/port binding or iPRA proof'},sort_keys=True,indent=2))
