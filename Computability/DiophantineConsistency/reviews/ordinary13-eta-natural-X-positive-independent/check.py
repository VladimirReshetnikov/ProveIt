#!/usr/bin/env python3
"""Independent source/graph and bounded arithmetic controls; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src':'e3bace196b09c86927bd178c279111ab4c97d076a18711c676ff127f002fe063',
'research/ordinary13-eta-natural-X-positive-model-draft/README.md':'ae697e629c841463f07ef68e8f67ce8ae30faf9275f7b0f0965564e2919c1162',
'research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src':'c30a9d4fe05ca8878e7681f1987b27e51af5db5bc4366d65b8cf050589636c63',
'research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src':'144b5447d8fde7f6384e3fb5ae8311bc051bf563190d204db3dad4810df5914b',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src':'7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/ModelRelationCombining.lean':'559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6',
'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean':'4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
x=s['research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src']
for t in ['theorem witness_positive','(hbeta : 0<(p 0:V))','EtaNaturalJPositiveDraft.J_positive p v hz',
 'let z : DiffRing V := (graph pp).d.evalRing e','ι (3+4*Y p v)*shiftRing p v',
 'EtaNaturalUnitBridgeDraft.signed_norms pp v hz','Residue90XZeroArithmeticDraft.xzero_impossible (q p v) (Y p v) (c p v)',
 'theorem X_positive','0<q p v*v 6']:
 assert t in x,t
z=s['research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src']
assert '''theorem xzero_impossible (q Y c : V) (z t : DiffRing V)
    (hq : 2≤q) (hY : q^3≤Y)
    (hshape : z=ι (Y*(q*q))*(ι Y*ι c)+ι (3+4*Y)*t)
    (hnorm : z*z=ι (Y*(q*q))*ι (Y*(q*q))*
      (1+(ι (3+4*Y)+ι Y*ι Y)*(ι c*ι c))) : False''' in z
assert 'ModelRelationCombining.sq_dvd_sq' in z and 'Trace75IntegralTransport.natural_dvd_of_signed' in z
assert 'theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0)' in s['Lean/DiophantineConsistency/ModelRelationCombining.lean']
assert 'theorem natural_dvd_of_signed (a b : V)' in s['Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean']
assert 'theorem J_positive (p : Fin 4 → ℕ)' in s['research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src']
assert 'theorem signed_norms' in s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rows={r[0]:r for r in g['source']}
for row in [['X','*','q','n_w'],['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],['r0','-','kbase','R'],['shift','-','g54','r0'],['Dstar','+','g58','g59']]:assert rows[row[0]]==row
rng=random.Random(212936);eta_zero=0
for i in range(400):
 e={n:rng.randrange(0,5) for n in g['witnesses']+g['fixed_numerals']};e['n_J']=rng.randrange(1,5);e['beta']=rng.randrange(1,7);e['n_w']=0
 if i%2==0:e['n_eta']=0
 eta_zero+=e['n_eta']==0
 for n,op,l,r in g['source']:
  l=l if isinstance(l,int) else e[l];r=r if isinstance(r,int) else e[r]
  e[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 q,Y=e['q'],e['Y'];U=Y*q*q;H=3+4*Y;t=U*e['n_gamma']-(e['n_eta']+e['n_zeta']-e['R'])
 assert q>=2 and Y>=q**3 and e['a']==Y and e['U']==U and e['Delta']==H+Y*Y
 assert e['Dstar']==U*Y*e['c']+H*t
 assert 3*q*q<H and U%H!=0
bounds=0
for q in range(2,80):
 for offset in range(17):
  Y=q**3+offset;U=Y*q*q;H=3+4*Y
  assert 4*U==(H-3)*q*q and 0<3*q*q<H and U%H!=0
  bounds+=1
print(json.dumps({'source_sha256':pins,'actual_prototype_carrier_controls':400,'eta_zero_controls':eta_zero,'divisibility_size_controls':bounds,'lean_executed':False,'scope':'source signatures and finite controls; no Lean proof, graph zero, provider build or iPRA endpoint'},sort_keys=True,indent=2))
