from pathlib import Path
from hashlib import sha256
import json,itertools
p=Path('research/ordinary13-eta-natural-J-positive-model-draft')
fs=[p/'EtaNaturalJPositive.lean.src',p/'README.md',
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('Lean/DiophantineConsistency/Compact44/P72Root.lean')]
s=[f.read_text() for f in fs]
for x in ['theorem J_positive','(p : Fin 4 → ℕ)','v 0=0','(p 1:V)',
 'EtaNaturalUnitBridgeDraft.signed_norms','(graph pp).b.evalRing e=0',
 '(graph pp).z.evalRing e=','mul_self_eq_zero.mp']:
 assert x in s[0],x
assert 'theorem signed_norms (p : Fin 4 → ℤ)' in s[3]
g=json.loads(s[4]);r={row[0]:row for row in g['source']}
for row in [['F','+','n_F',1],['alpha','+','n_alpha',1],['qm','*','n_J','beta'],
 ['q','+',1,'qm'],['X','*','q','n_w'],['qF','-','q','F'],['C','-','qF','alpha'],
 ['g26','+','X','K0'],['g27','*','C','g26'],['Bt','-','g27','F'],
 ['g32','*','qm','folded_g31'],['Z','-','g32','Bt']]:assert r[row[0]]==row
assert g['witnesses'].index('n_J')==0 and g['fixed_numerals'].index('K0')==1
count=0
for f,alpha,x,K in itertools.product(range(1,8),range(1,8),range(8),range(8)):
 C=1-f-alpha;bt=C*(x+K)-f;z=-bt
 assert C<=0 and bt<0 and z>=f>0 and 1+z*z>1
 count+=1
f=alpha=1;x=0;K=-1;C=1-f-alpha;bt=C*(x+K)-f;assert bt==0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'positive_K0_controls':count,'negative_K0_first_factor_counterexample':True,
 'lean_executed':False,'status':'unelaborated; unit bridge and model providers remain open'},sort_keys=True,indent=2))
