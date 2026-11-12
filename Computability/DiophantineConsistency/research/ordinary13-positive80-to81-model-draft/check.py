from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-positive80-to81-model-draft')
fs=[p/'generate.py',p/'PositiveSquare81Graph.lean.src',p/'Positive80To81Transport.lean.src',p/'README.md',
Path('research/ordinary13-unit-product80/candidate.json'),
Path('research/ordinary13-residue-first81/candidate.json'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),
Path('research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-eta85-to-positive80-composition-draft/Eta85ToPositive80.lean.src')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='positive81-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[5]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
g80,g81,g85=map(json.loads,s[4:7]);assert len(g80['source'])==80 and len(g81['source'])==81
assert g80['witnesses']==g81['witnesses'] and g80['fixed_numerals']==g81['fixed_numerals']
assert g80['source'][:73]==g81['source'][:73]
assert g81['source'][-8:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]
for x in ['import Eta85ToPositive80','theorem field_equalities','theorem output81','theorem output80',
 'theorem zero80_to81','EtaNaturalUnitBridgeDraft.residuals_zero','theorem zero81_to80',
 'theorem sameNoZero','(h81 : PolynomialBridge','Eta85ToPositive80Draft.native85']:
 assert x in s[2],x
assert 'theorem residuals_zero' in s[9]
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e
rng=random.Random(8081);direct={3,8,11}
for _ in range(400):
 vals=[rng.randrange(1,14) for _ in range(13)];ports={k:rng.randrange(14) for k in g80['fixed_numerals']}
 v=dict(zip(g80['witnesses'],vals));v.update(ports)
 down=[x if i in direct else x-1 for i,x in enumerate(vals)]
 for i in [0,12,6,9]:down[i]+=1
 w=dict(zip(g85['witnesses'],down));w.update(ports)
 e80=calc(g80,v);e81=calc(g81,v);e85=calc(g85,w)
 for key in ['A0','A1','Fa','g72']:assert e80[key]==e81[key]==e85[key]
 a,b,c,d=(e81[x] for x in ['A0','A1','Fa','g72'])
 assert e81['out']==(a*a+b*b+(c-1)**2+d*d)%P
 assert e80['out']==((1+a)*(1+b)*c*(1+d)-1)%P
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'shared_prefix_rows':73,'positive_factor_controls':400,'lean_executed':False,
 'status':'unelaborated; 81 parent bridge and all graph/model providers remain open'},sort_keys=True,indent=2))
