#!/usr/bin/env python3
"""Exact finite controls for a preserving-Y normalization obstruction."""
import hashlib,json,operator,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={
 'research/p64-qcube72-forward-graph-draft/FreeMainGraphForward.lean':'eeb3d8314793b90e2d6a33d928fb983d5bed6b145c5f9e09d3e9766a7a14c3e5',
 'research/p64-qcube72-free-main-candidate/P64QCube72FreeForward.lean':'7256e6dd921e74a3ecf013f60e4ab512b6313d728c9538665f8f629fcfbd408c',
 'research/p64-qcube72-free-main-candidate/P64QCube72FreeBinding.lean':'342933823c3e4f1e55289abd0347628cf81f0188bd35ac7d2c2006b005d7df7a',
 'research/p64-qcube72-divisible-q-no-old-gamma-draft/FreeMainDivisibleQNoOldGamma.lean':'c986b3c588a74730991681805d906e611435915fb54fd81128a4e67779720564',
 'research/p64-qcube76y-fixed-q-not-three-draft/FreeMain76FixedQNotThree.lean':'2366738263d44e4f47151cdd0bddcdc6df5248f03f21f90b225d03494e647e0a',
 'Lean/DiophantineConsistency/Compact44/P64Root.lean':'afcbb52982e7c1334e615029e4af554fbb53c86ee07e77070212d2edf47118f9',
 'research/p64-qcube72-free-main-candidate/graph.json':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 'research/p64-qcube76-independent-y-candidate/graph.json':'196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'}
for f,h in pins.items():
 if hashlib.sha256((root/f).read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+f)
if (pow(2,590069,3)-1)%3!=1:raise RuntimeError('fixed beta residue')
def cube_free(n):
 p=2
 while p*p*p<=n:
  if n%(p*p*p)==0:return False
  p+=1
 return True
rigidity=0
for beta in range(1,61):
 for J in range(1,beta+2):
  q=beta*J+1
  for Jp in range(1,J+1):
   qp=beta*Jp+1
   for s in range(1,16):
    if not cube_free(s):continue
    if (q**3*s)%(qp**3)==0 and qp!=q:raise RuntimeError('cube-free preserving-Y rigidity')
    rigidity+=1
# Non-cube-free scale can exchange q and beta+1 while preserving Y.
for beta in range(1,101):
 q=2*beta+1; qp=beta+1; s=qp**3; sp=q**3
 if qp==q or cube_free(s) or q**3*s!=qp**3*sp:raise RuntimeError('non-cube-free control')
old=json.loads((root/'research/p64-qcube76-independent-y-candidate/graph.json').read_bytes())
new=json.loads((root/'research/p64-qcube72-free-main-candidate/graph.json').read_bytes());ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def ev(a,v):
 d=v.copy()
 for name,op,x,y in a['source']:d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
 return d
rng=random.Random(726172); controls=0
for _ in range(160):
 beta=rng.randrange(3,10);J=rng.randrange(1,5);q=beta*J+1;F=rng.randrange(1,q-1);alpha=rng.randrange(1,q-F)
 v={k:rng.randrange(1,5) for k in old['witnesses']};v.update({'beta':beta,'K0':rng.randrange(0,5),'MC':rng.randrange(0,beta),'MF':rng.randrange(0,2*beta),'J':J,'F':F,'alpha':alpha})
 d=ev(old,v);h=d['main_gap']
 if h<=0:raise RuntimeError('control gap not positive')
 u=v.copy();u.pop('gamma');u['h']=h;e=ev(new,u)
 if e['q']!=d['q'] or e['Y']!=d['Y'] or e['k']!=d['k'] or e['R']!=d['R']:raise RuntimeError('coordinates changed')
 if h+d['k']!=d['U']*v['gamma']+d['R']+1:raise RuntimeError('old carrier relation')
 if e['polynomial']!=d['polynomial']:raise RuntimeError('binding mismatch')
 controls+=1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','cube_free_rigidity_candidate_tests':rigidity,'non_cube_free_swap_controls':100,'forward_graph_controls':controls,'fixed_beta_mod_3':1,'pins':pins,'scope':'Finite number-theory and forward-binding controls; fixed-beta 76 exclusion is a checked Lean theorem; preserving-Y argument is external, with no 72 zero existence claim.'},sort_keys=True))
