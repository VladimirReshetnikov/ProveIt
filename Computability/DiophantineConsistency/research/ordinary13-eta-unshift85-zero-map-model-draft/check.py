from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-eta-unshift85-zero-map-model-draft')
fs=[p/'generate.py',p/'EtaShifted86Graph.lean.src',p/'EtaUnshift85Transport.lean.src',p/'README.md',
Path('research/ordinary13-natural-forced-w86/candidate.json'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src'),
Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),
Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean'),
Path('Lean/DiophantineConsistency/IPRAExpressionNative.lean')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='eta-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[4]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
old=json.loads(s[4]);new=json.loads(s[5]);assert len(old['source'])==86 and len(new['source'])==85
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
assert old['witnesses'][9]=='n_eta'
assert [[('n_eta' if x=='eta' else x) for x in row] for row in old['source'] if row!=['eta','+','n_eta',1]]==new['source']
for x in ['if i=9 then v i+1 else v i','if i=9 then v i-1 else v i',
 'theorem evaluation','def ForcedEta','(heta : ForcedEta K)','(hparent : PolynomialBridge',
 'compact_no_zero_iff','compact_sameNoZero','HAExpressionNoZeroEquiv.bridge',
 'IPRAExpressionNative.equivalence_of_bridge','ports K j']:
 assert x in s[2],x
assert 'theorem bridge' in s[8] and 'theorem equivalence_of_bridge' in s[9]
prime=1000000007
def calc(g,v):
 e={k:z%prime for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%prime if isinstance(l,int) else e[l];y=r%prime if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%prime
 return e[g['output']]
rng=random.Random(1937)
for _ in range(500):
 v={k:rng.randrange(0,20) for k in old['witnesses']+old['fixed_numerals']}
 w=dict(v);w['n_eta']+=1
 assert calc(old,v)==calc(new,w)
 assert w['n_eta']>0 and w['n_eta']-1==v['n_eta']
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'parent_rows':86,'prototype_rows':85,'shift_controls':500,'same_natural_compact_ports':True,
 'eta_forcing_and_parent_bridge_explicit':True,'lean_executed':False,
 'status':'unelaborated; forcing, parent bridge and provider provenance remain open'},sort_keys=True,indent=2))
