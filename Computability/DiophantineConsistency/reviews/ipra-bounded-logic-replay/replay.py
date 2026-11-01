#!/usr/bin/env python3
"""Source-directed selector replay on a pinned native open-decision provider."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]; SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/ipra-bounded-shape-3y547v7p'); PACKAGE=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib'); LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
names=['IPRABoundedLogic','IPRABoundedLogicChecks']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
parent=json.loads((P/'state.json').read_text()); assert parent['status']=='PASS'
source={n:sha(SRC/(n+'.lean')) for n in names}
# Traverse literal local imports from all endpoint sources; this is a source
# observation, not authentication of the inherited objects' production.
seen={}; missing=[]
def visit(n):
 if n in seen:return
 p=SRC/(n+'.lean')
 if not p.is_file():missing.append(n);return
 s=p.read_text();seen[n]=sha(p)
 for dep in re.findall(r'^import\s+DiophantineConsistency\.([A-Za-z0-9_]+)',s,re.M):visit(dep)
for n in names:visit(n)
assert not missing,missing
objects={p.name:sha(p) for p in (P/'lib/DiophantineConsistency').glob('*.olean') if p.name not in {n+'.olean' for n in names}}
external={n:sha(P/'lib'/n) for n in ['Foundation/FirstOrder/Arithmetic/Schemata.olean','Foundation/FirstOrder/NegationTranslation/GoedelGentzen.olean']}
parenth=sha(P/'state.json'); leanh=sha(LEAN); driverh=sha(__file__)
for row in parent['records']:
 n=row['name']; assert sha(SRC/(n+'.lean'))==parent['source_sha256'][n]; assert sha(P/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'];assert sha(P/'logs'/(n+'.log'))==row['log_sha256']
w=Path(tempfile.mkdtemp(prefix='ipra-bounded-logic-'));lib=w/'lib';dest=lib/'DiophantineConsistency';dest.mkdir(parents=True);src=w/'src/DiophantineConsistency';src.mkdir(parents=True);logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py')
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for p in top.iterdir():
  if p.name not in {n+'.olean' for n in names}:(dest/p.name).symlink_to(p.resolve(),target_is_directory=p.is_dir())
for n in names:shutil.copyfile(SRC/(n+'.lean'),src/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','parent':str(P),'parent_state_sha256':parenth,'lean_sha256':leanh,'driver_sha256':driverh,'source_sha256':source,'observed_local_closure':seen,'selected_parent_objects':objects,'external_anchors':external,'records':[],'scope':'Derives native GG backward comparison for a bounded existential from its bounded child comparison, for either hierarchy polarity, and provides a disjunction composition. Full recursive comparison and actual rho binding remain open. All selected inherited project objects and observed local sources are hashed, but their mutual production provenance and Foundation/package transitive ancestry are inherited.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def audit():
 assert sha(P/'state.json')==parenth and sha(LEAN)==leanh and sha(__file__)==driverh and sha(w/'driver.py')==driverh
 assert all(sha(SRC/(n+'.lean'))==h for n,h in seen.items())
 assert all(sha(src/(n+'.lean'))==h and sha(logs/(n+'.lean'))==h for n,h in source.items())
 assert all(sha(P/'lib/DiophantineConsistency'/n)==h and sha(dest/n)==h for n,h in objects.items())
 assert all(sha(P/'lib'/n)==h and sha(lib/n)==h for n,h in external.items())
save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PACKAGE),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in names:
  obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
  with log.open('w') as f:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(src.parent),str(src/(n+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  state['records'].append({'name':n,'exit':r.returncode,'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'seconds':time.monotonic()-t});save();print(n,r.returncode,flush=True)
  s=log.read_text();assert r.returncode==0 and 'warning:' not in s and 'error:' not in s and 'sorryAx' not in s
  if n.endswith('Checks'):
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
   assert len(blocks)==3,(s,blocks)
   assert all(set(x.strip() for x in b.split(','))=={'propext','Classical.choice','Quot.sound'} for b in blocks),(s,blocks)
 audit();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();raise
