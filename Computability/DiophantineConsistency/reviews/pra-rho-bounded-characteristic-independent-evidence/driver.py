#!/usr/bin/env python3
"""Replay the actual bounded-rho classical characteristic existence theorem."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/ipra-deep-bound-join-4sekpn2c');PACKAGE=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
parent=json.loads((P/'state.json').read_text());assert parent['status']=='PASS'
names=['PRARhoBoundedCharacteristic','PRARhoBoundedCharacteristicChecks']
sourceh={n:sha(SRC/(n+'.lean')) for n in names}
parenth=sha(P/'state.json');leanh=sha(LEAN)
for row in parent['records']:
 n=row['name'];assert sha(P/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']
 assert sha(P/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256']
 assert sha(P/'logs'/(n+'.log'))==row['log_sha256']
anchors=['FoundationHAConsistencyNormalization','ParsonsHierarchyMap','PRABoundedFormula','StrictSigmaOneInduction']
anch={n:sha(P/'lib/DiophantineConsistency'/(n+'.olean')) for n in anchors}
external={n:sha(P/'lib'/n) for n in ['Foundation/FirstOrder/Arithmetic/Schemata.olean','Foundation/FirstOrder/NegationTranslation/GoedelGentzen.olean']}
w=Path(tempfile.mkdtemp(prefix='pra-rho-bounded-characteristic-'));lib=w/'lib';dest=lib/'DiophantineConsistency';dest.mkdir(parents=True);src=w/'src/DiophantineConsistency';src.mkdir(parents=True);logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py')
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for p in top.iterdir():
  if p.name not in {n+'.olean' for n in names}:(dest/p.name).symlink_to(p.resolve(),target_is_directory=p.is_dir())
for n in names:shutil.copyfile(SRC/(n+'.lean'),src/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','parent':str(P),'parent_state_sha256':parenth,'lean_sha256':leanh,'source_sha256':sourceh,'direct_project_anchors':anch,'external_anchors':external,'records':[],'scope':'For the exact mapped bounded Foundation ZFC refutation matrix, prove its Sigma-zero hierarchy certificate and existence of a classical PRA Boolean characteristic code. Does not prove native characteristic correctness or the consistency equivalence. Selected provider objects and direct external anchors are guarded; inherited project, Foundation and package source/object ancestry remains historical.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def audit():
 assert sha(P/'state.json')==parenth and sha(LEAN)==leanh
 assert all(sha(SRC/(n+'.lean'))==h and sha(src/(n+'.lean'))==h and sha(logs/(n+'.lean'))==h for n,h in sourceh.items())
 assert all(sha(P/'lib/DiophantineConsistency'/(n+'.olean'))==h and sha(dest/(n+'.olean'))==h for n,h in anch.items())
 assert all(sha(P/'lib'/n)==h and sha(lib/n)==h for n,h in external.items())
 assert all(sha(P/'src/DiophantineConsistency'/(r['name']+'.lean'))==r['source_sha256'] and sha(P/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in parent['records'])
save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PACKAGE),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in names:
  obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
  with log.open('w') as f:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(src.parent),str(src/(n+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  state['records'].append({'name':n,'exit':r.returncode,'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'seconds':time.monotonic()-t});save();print(n,r.returncode,flush=True)
  assert r.returncode==0 and 'warning:' not in log.read_text() and 'error:' not in log.read_text() and 'sorryAx' not in log.read_text()
 audit();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();raise
