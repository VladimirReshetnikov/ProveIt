#!/usr/bin/env python3
"""Multi-namespace source-directed native 86/87 endpoint replay."""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
D=Path(__file__).resolve().parent;M=D/'manifest.json';R=D.parents[3]
P=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads(M.read_text());mh=h(M);dh=h(__file__);assert dh==m['driver_sha256']
assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256']
assert json.loads((P/'state.json').read_text())['status']=='PASS'
assert all(h(R/p)==m['source_sha256'][n] for n,p in m['source_files'].items())
inventory=lambda: {str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')}
assert inventory()==set(m['parent_objects'])
assert all(h(P/'lib'/f)==v for f,v in m['parent_objects'].items())
assert all(h(PKG/f)==v['sha256'] and str((PKG/f).resolve())==v['resolved_path'] for f,v in m['external_direct'].items())
w=Path(tempfile.mkdtemp(prefix='ipra-adaptive-native-current-'));lib=w/'lib';lib.mkdir();src=w/'src';src.mkdir();logs=w/'logs';logs.mkdir()
(w/'driver.py').write_bytes(Path(__file__).read_bytes());(w/'manifest.json').write_bytes(M.read_bytes());exclude={n.replace('.','/')+'.olean' for n in m['order']}
for f in m['parent_objects']:
 if f not in exclude:
  dest=lib/f;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to((P/'lib'/f).resolve())
for n in m['order']:
 dest=src/(n.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((R/m['source_files'][n]).read_bytes())
state={'status':'RUNNING','parent':str(P),'parent_state_sha256':m['parent_state_sha256'],'manifest_sha256':mh,'driver_sha256':dh,'records':[],'scope':m['scope']}
def save():(w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')
def audit():
 assert h(M)==mh and h(__file__)==dh and h(w/'driver.py')==dh and h(w/'manifest.json')==mh
 assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256']
 assert all(h(R/p)==m['source_sha256'][n] for n,p in m['source_files'].items())
 assert all(h(D/'sources'/(n.replace('.','/')+'.lean'))==m['source_sha256'][n] and h(src/(n.replace('.','/')+'.lean'))==m['source_sha256'][n] for n in m['order'])
 assert inventory()==set(m['parent_objects'])
 assert all(h(P/'lib'/f)==v and (f in exclude or h(lib/f)==v) for f,v in m['parent_objects'].items())
 assert all(h(PKG/f)==v['sha256'] and str((PKG/f).resolve())==v['resolved_path'] for f,v in m['external_direct'].items())
 assert all(h(lib/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and h(logs/(r['name'].replace('.','_')+'.log'))==r['log_sha256'] for r in state['records'] if r['exit']==0)
save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in m['order']:
  obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n.replace('.','_')+'.log');dep={};t=time.monotonic()
  for mod in m['direct_imports'][n]:
   rel=Path(mod.replace('.','/')+'.olean');path=lib/rel if (lib/rel).exists() else PKG/rel
   assert path.exists(),str(path);dep[mod]={'sha256':h(path),'resolved_path':str(path.resolve())}
  with log.open('w') as f:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(src),str(src/(n.replace('.','/')+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  state['records'].append({'name':n,'exit':r.returncode,'object_sha256':h(obj) if obj.exists() else None,'log_sha256':h(log),'direct_imports':dep,'seconds':time.monotonic()-t});save();print(n,r.returncode,flush=True)
  s=log.read_text();assert r.returncode==0 and 'warning:' not in s and 'error:' not in s and 'sorryAx' not in s
  if n=='DiophantineConsistency.IPRAAdaptiveNativeZFCChecks':
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',s);assert len(blocks)==2,(s,blocks)
   assert all(set(x.strip() for x in b.split(','))=={'propext','Classical.choice','Quot.sound'} for b in blocks),(s,blocks)
 audit();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();raise
