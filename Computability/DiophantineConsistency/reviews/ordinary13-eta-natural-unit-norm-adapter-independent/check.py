#!/usr/bin/env python3
"""Independent source-interface and polynomial-cut audit; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-unit-norm-adapter-draft/EtaNaturalUnitNormAdapter.lean.src':'07501449ec0a7f7242107dc2f21ab0994c8adbc55013f409055c3ad2b6969214',
'research/ordinary13-eta-natural-unit-norm-adapter-draft/README.md':'3804a6fc5ace584e59f49ffc9ec7f58c91082631fc6e1711912c340dc8f9ddc0',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src':'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a',
'research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src':'7cb45a1766cedf64f1ad6f1a11977ec66990a9c7977f41a9e100a6d36742845e',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
ad=s['research/ordinary13-eta-natural-unit-norm-adapter-draft/EtaNaturalUnitNormAdapter.lean.src']
bridge=s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
for t in ['theorem first_norm_of_unit','theorem main_pair_of_unit','theorem main_natural_of_unit','theorem rank_congruence_of_main_unit','(hb : 0<b)','(hU : 0<U q Y)','(hq : 0<q) (hY : Y=q^3*s) (hY8 : 8≤Y) (hk : 0<k)',
 'U q Y*(X+a X Y*c Y eta k)+H X Y*(U q Y*gamma+R+1)',
 'Residue90SignedNormsDraft.first_natural_norm','Residue90SignedNormsDraft.main_pair_norm','Residue90SignedNormsDraft.main_natural_norm','EtaZeroEarlyCongruenceDraft.rank_congruence_of_main_norm']:
 assert t in ad,t
for t in ['theorem factor_units','theorem signed_norms','z*z=b*b*(1+ell*(ell+k))','d*d=U*U*(1+Delta*(c*c))','I*I=Delta*(f*f-1)']:
 assert t in bridge,t
sd=s['research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src']
assert '(hn : z*z=(ι b)*(ι b)*ι (1+m*(m+1)*k*k))' in sd
assert '(hn : (ι P-ι N)*(ι P-ι N) = (ι U)*(ι U)*(1+ι Delta*(ι c*ι c)))' in sd
assert 'theorem main_natural_norm (U Delta c P N : V) (hU : 0<U)' in sd
ce=s['research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src']
assert 'theorem rank_congruence_of_main_norm (q X Y k R eta gamma s : V)' in ce
assert '(hq : 0<q) (hY : Y=q^3*s) (hY8 : 8≤Y) (hk : 0<k)' in ce
# Canonical sparse polynomial arithmetic proves each cut as a ring identity.
N=9
class Poly:
 def __init__(self,t):self.t={m:v for m,v in t.items() if v}
 def __add__(self,o):
  o=up(o);r=self.t.copy()
  for k,v in o.t.items():r[k]=r.get(k,0)+v
  return Poly(r)
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.t.items()})
 def __sub__(self,o):return self+-up(o)
 def __rsub__(self,o):return up(o)+-self
 def __mul__(self,o):
  o=up(o);r={}
  for m,v in self.t.items():
   for n,w in o.t.items():
    k=tuple(a+b for a,b in zip(m,n));r[k]=r.get(k,0)+v*w
  return Poly(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.t==up(o).t
def up(x):return x if isinstance(x,Poly) else Poly({(0,)*N:x})
def var(i):return Poly({tuple(1 if j==i else 0 for j in range(N)):1})
X,Y,k,U,a,c,H,R,gamma=[var(i) for i in range(N)]
m=X*Y*Y;ell=(X*Y)*(Y*k)
assert ell*(ell+k)==m*(m+1)*k*k
kbase=k-1
D=U*(X+a*c)+H*(U*gamma-(kbase-R))
P=U*(X+a*c)+H*(U*gamma+R+1);N0=H*k
assert D==P-N0
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(34142)
for j in range(200):
 vals={n:rng.randrange(0,4) for n in g['witnesses']+g['fixed_numerals']}
 vals['beta']=rng.randrange(6,12);vals['n_J']=rng.randrange(1,4);vals['n_F']=rng.randrange(0,2);vals['n_alpha']=rng.randrange(0,2)
 if j%2==0:vals['n_eta']=0
 for name,op,l,r in g['source']:
  l=l if isinstance(l,int) else vals[l];r=r if isinstance(r,int) else vals[r]
  vals[name]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 assert vals['F']+vals['alpha']<vals['q'] and vals['R']>=0
 X,Y,k=vals['X'],vals['Y'],vals['k'];m=X*Y*Y
 P=vals['U']*(X+vals['a']*vals['c'])+vals['H']*(vals['U']*vals['n_gamma']+vals['R']+1)
 assert vals['Dstar']==P-vals['H']*k
 assert vals['A0']==vals['Z']**2-vals['qm']**2*(1+m*(m+1)*k*k)
 assert vals['A1']==(P-vals['H']*k)**2-vals['U']**2*(1+vals['Delta']*vals['c']**2)
print(json.dumps({'source_sha256':pins,'exact_free_polynomial_cuts':2,'sampled_prototype_controls':200,'eta_zero_samples':100,'lean_executed':False,'scope':'source/interface, ring identities, finite controls; no embedding theorem, Lean, provider build, zero map, or iPRA proof'},sort_keys=True,indent=2))
