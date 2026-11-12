from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-eta-natural-X-positive-model-draft')
fs=[p/'EtaNaturalXPositive.lean.src',p/'README.md',
Path('research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src'),
Path('research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['theorem witness_positive','EtaNaturalJPositiveDraft.J_positive','(hbeta : 0<(p 0:V))',
 'EtaNaturalUnitBridgeDraft.signed_norms','(graph pp).d.evalRing e','shiftRing',
 'Residue90XZeroArithmeticDraft.xzero_impossible','theorem X_positive','0<q p v*v 6']:
 assert x in s[0],x
assert 'theorem xzero_impossible' in s[3] and '(hq : 2≤q)' in s[3] and '(hY : q^3≤Y)' in s[3]
g=json.loads(s[6]);r={row[0]:row for row in g['source']}
for row in [['X','*','q','n_w'],['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],
 ['r0','-','kbase','R'],['shift','-','g54','r0'],['Dstar','+','g58','g59']]:
 assert r[row[0]]==row
rng=random.Random(7509); n=0; eta_zero=0
for _ in range(500):
 v={key:rng.randrange(0,4) for key in g['witnesses']+g['fixed_numerals']}
 v['n_J']=rng.randrange(1,5);v['beta']=rng.randrange(1,5);v['n_w']=0
 if n%2==0:v['n_eta']=0
 e=v.copy()
 for name,op,l,r0 in g['source']:
  a=l if isinstance(l,int) else e[l]; b=r0 if isinstance(r0,int) else e[r0]
  e[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 q=1+v['n_J']*v['beta'];Y=q**3*(v['n_s']+1);U=Y*q*q;H=3+4*Y
 k=v['n_eta']+v['n_zeta']+1;c=v['n_eta']+Y*k
 rank=(v['n_alpha']+1+(q-(v['n_F']+1))*(q-1))*(q*q-1)+v['n_J']*(v['MC']+v['MF']*q)
 t=U*v['n_gamma']-(v['n_eta']+v['n_zeta']-rank)
 assert e['Dstar']==U*Y*c+H*t and e['c']==c and e['Delta']==H+Y*Y
 assert q>=2 and Y>=q**3 and 3*q*q<H and U%H!=0
 n+=1;eta_zero+=v['n_eta']==0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'actual_graph_controls':n,'eta_zero_controls':eta_zero,'lean_executed':False,
 'status':'unelaborated; graph unit bridge and model providers remain open'},sort_keys=True,indent=2))
