#!/usr/bin/env python3
"""Replay bounded-induction project suffix on a frozen 848-module provider."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time,re
P=Path('/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt'); PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
D=Path(__file__).resolve().parent; M=D/'manifest.json'; R=D.parents[3]
SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads(M.read_text());mh=sha(M);dh=sha(__file__);assert dh==m['driver_sha256']
assert sha(P/'state.json')==m['parent_state_sha256'] and sha(LEAN)==m['lean_sha256']
assert json.loads((P/'state.json').read_text())['status']=='PASS'
assert all(sha(SRC/(n+'.lean'))==h for n,h in m['observed_sources'].items())
assert {str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')} == set(m['parent_objects'])
assert all(sha(P/'lib'/f)==h for f,h in m['parent_objects'].items())
assert all(sha(PKG/f)==info['sha256'] and str((PKG/f).resolve())==info['resolved_path'] for f,info in m['external_direct'].items())
w=Path(tempfile.mkdtemp(prefix='ipra-bounded-induction-postmerge-'));lib=w/'lib';lib.mkdir();dest=lib/'DiophantineConsistency';dest.mkdir();src=w/'src/DiophantineConsistency';src.mkdir(parents=True);logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(M,w/'manifest.json')
exclude={n+'.olean' for n in m['order']}
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for p in top.iterdir():
  if p.name not in exclude:(dest/p.name).symlink_to(p.resolve(),target_is_directory=p.is_dir())
for n in m['order']:
 shutil.copyfile(SRC/(n+'.lean'),src/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','parent':str(P),'parent_state_sha256':m['parent_state_sha256'],'manifest_sha256':mh,'driver_sha256':dh,'records':[],'scope':m['scope']}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def audit():
 assert sha(M)==mh and sha(__file__)==dh and sha(w/'driver.py')==dh and sha(w/'manifest.json')==mh
 assert sha(P/'state.json')==m['parent_state_sha256'] and sha(LEAN)==m['lean_sha256']
 assert all(sha(SRC/(n+'.lean'))==h for n,h in m['observed_sources'].items())
 assert all(sha(D/'sources/DiophantineConsistency'/(n+'.lean'))==m['observed_sources'][n] for n in m['order'])
 assert {str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')} == set(m['parent_objects'])
 assert all(sha(src/(n+'.lean'))==m['observed_sources'][n] and sha(logs/(n+'.lean'))==m['observed_sources'][n] for n in m['order'])
 assert all(sha(P/'lib'/f)==h and sha(lib/f)==h for f,h in m['parent_objects'].items())
 assert all(sha(PKG/f)==info['sha256'] and str((PKG/f).resolve())==info['resolved_path'] for f,info in m['external_direct'].items())
 assert all(sha(dest/(r['name']+'.olean'))==r['object_sha256'] and sha(logs/(r['name']+'.log'))==r['log_sha256'] for r in state['records'] if r['exit']==0)
save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in m['order']:
  obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
  dep={}
  for mod in m['direct_imports'][n]:
   rel=Path(mod.replace('.','/')+'.olean');path=lib/rel if (lib/rel).exists() else PKG/rel
   assert path.exists(),str(path);dep[mod]={'sha256':sha(path),'resolved_path':str(path.resolve())}
  with log.open('w') as f:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(src.parent),str(src/(n+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  state['records'].append({'name':n,'exit':r.returncode,'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'direct_imports':dep,'seconds':time.monotonic()-t});save();print(n,r.returncode,flush=True)
  s=log.read_text();assert r.returncode==0 and 'warning:' not in s and 'error:' not in s and 'sorryAx' not in s
  if n=='IPRABoundedInductionChecks':
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',s);assert len(blocks)==3,(s,blocks)
   assert all(set(x.strip() for x in b.split(','))=={'propext','Classical.choice','Quot.sound'} for b in blocks),(s,blocks)
 audit();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();raise
