#!/usr/bin/env python3
"""Independent exact field, root-interface and algebra review; no Lean."""
from pathlib import Path
import hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src':'b97bba84dc1aafe0dd8ee6eef287e003f6666f5e9ef645a74970f77bdbec1c61',
'research/ordinary13-eta-natural-graph-norm-model-draft/README.md':'9ca86305f714bfdfdb7a3085bae043aa225f2946198c8226dea5011e84fd0e31',
'research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src':'e3bace196b09c86927bd178c279111ab4c97d076a18711c676ff127f002fe063',
'research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src':'c30a9d4fe05ca8878e7681f1987b27e51af5db5bc4366d65b8cf050589636c63',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src':'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src']
for t in ['theorem field_b','theorem field_k','theorem field_ell','theorem field_U','theorem field_c','theorem field_delta',
 '(graph (pp p)).z.evalRing (emb v)','(graph (pp p)).d.evalRing (emb v)',
 '(hb : 0<v 0*(p 0:V))','(hU : 0<U p v)','(hbeta : 0<(p 0:V))',
 'Residue90SignedNormsDraft.first_natural_norm','Residue90SignedNormsDraft.signed_norm_quotient','EtaNaturalJPositiveDraft.J_positive']:
 assert t in d,t
q=s['research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src']
assert 'theorem signed_norm_quotient (scale N : V) (z : DiffRing V) (hs : 0<scale)' in q
assert '∃ a t : V, z*z=ι (a*a) ∧ a=scale*t ∧ t*t=N' in q
assert 'theorem first_natural_norm (b m k : V) (z : DiffRing V) (hb : 0<b)' in q
assert 'theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4)' in s['Lean/DiophantineConsistency/Compact44/P72Root.lean']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'])
lit=s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src']
body=lit.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1]
rows=[]
for line in body.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
 if m:
  name,a,op,b=m.groups();rows.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert rows==g['source']
assert '⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, k, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩' in lit
# Independently compare bounded evaluations at both eta=0 and eta>0.
rng=random.Random(94406);eta0=0
for j in range(240):
 e={n:rng.randrange(0,5) for n in g['witnesses']+g['fixed_numerals']}
 if j%2==0:e['n_eta']=0
 eta0+=e['n_eta']==0
 for name,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 q=1+e['n_J']*e['beta'];X=q*e['n_w'];Y=q**3*(e['n_s']+1);k=e['n_eta']+e['n_zeta']+1
 m=X*Y*Y;A=X*Y+Y
 assert e['qm']==e['n_J']*e['beta'] and e['k']==k and e['ell']==m*k
 assert e['U']==Y*q*q and e['c']==e['n_eta']+Y*k and e['Delta']==3+4*A+A*A
 assert 1+e['ell']*(e['ell']+k)==1+m*(m+1)*k*k
 assert e['A0']==e['Z']**2-e['qm']**2*(1+m*(m+1)*k*k)
 assert e['A1']==e['Dstar']**2-e['U']**2*(1+e['Delta']*e['c']**2)
print(json.dumps({'source_sha256':pins,'literal_rows_exact':len(rows),'prototype_field_controls':240,'eta_zero_controls':eta0,'lean_executed':False,'scope':'exact literal transcription, source-interface and bounded field controls; no all-model evaluation, Lean, provider build, zero maps or iPRA proof'},sort_keys=True,indent=2))
