from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-natural89-to-positive80-model-draft')
fs=[p/'generate.py',p/'PositiveUnit80Graph.lean.src',p/'Natural89Positive80Transport.lean.src',p/'README.md',
Path('research/ordinary13-unit-product80/candidate.json'),
Path('research/ordinary13-natural-unit-product89/candidate.json'),
Path('research/ordinary13-J88-to89-model-draft/JShifted89Graph.lean.src'),
Path('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),
Path('research/ordinary13-residue90-to82-model-draft/Residue90To82Transport.lean.src'),
Path('research/ordinary13-natural-unit-product89/README.md')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='positive80-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[4]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
g80,g89=map(json.loads,s[4:6]);assert len(g80['source'])==80 and len(g89['source'])==89
assert g80['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma']
assert g89['witnesses']==['n_'+x for x in g80['witnesses']]
direct={3,8,11}
for x in ['if i=3 ∨ i=8 ∨ i=11 then v i else v i+1','if i=3 ∨ i=8 ∨ i=11 then v i else v i-1',
 'theorem evaluation','def PositiveDirectReplacement','def DirectFY','def RReplacement',
 'theorem replacement_of_cuts','theorem compact_sameNoZero','(h80 : PolynomialBridge',
 'EtaUnshift85TransportDraft.ForcedEta K']:
 assert x in s[2],x
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e[g['output']]
rng=random.Random(8980)
for _ in range(500):
 vals=[rng.randrange(0,15) for _ in range(13)]; ports={k:rng.randrange(0,15) for k in g89['fixed_numerals']}
 n=dict(zip(g89['witnesses'],vals));n.update(ports)
 lifted=[x if i in direct else x+1 for i,x in enumerate(vals)]
 pos=dict(zip(g80['witnesses'],lifted));pos.update(ports)
 assert calc(g89,n)==calc(g80,pos)
 assert [x if i in direct else x-1 for i,x in enumerate(lifted)]==vals
for _ in range(100):
 vals=[rng.randrange(1,15) for _ in range(13)]
 down=[x if i in direct else x-1 for i,x in enumerate(vals)]
 assert [x if i in direct else x+1 for i,x in enumerate(down)]==vals
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'natural89_rows':89,'positive80_rows':80,'direct_positions':[3,8,11],
 'valuation_controls':500,'positive_inverse_controls':100,'lean_executed':False,
 'status':'unelaborated; f/y, r replacement and parent bridge remain open'},sort_keys=True,indent=2))
