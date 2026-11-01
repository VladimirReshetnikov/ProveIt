"""Exact bounded-rho client with selected and actually loaded package files pinned.

This pins bytes loaded by these Lean invocations, including .olean.private,
.olean.server and .ir. Parent project and package *source ancestry* remains
inherited historical; the trace does not certify unobserved dynamic executions.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/ipra-bounded-whole-rebase-peer-c5j94wtl');PKG=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
MANIFEST=R/'Computability/DiophantineConsistency/research/ipra-refutation-logic/bounded-rho-loaded-package.jsonl'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');STRACE=Path('/usr/bin/strace')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
parent=json.loads((P/'state.json').read_text());assert parent['status']=='PASS' and parent['author_rows_match']
parent_hash=sha(P/'state.json');manifest_hash=sha(MANIFEST);lean_hash=sha(LEAN);trace_hash=sha(STRACE)
package=[json.loads(x) for x in MANIFEST.read_text().splitlines() if x];assert len(package)==11316
package_map={x['path']:x for x in package};assert len(package_map)==len(package)
names=['IPRABoundedRhoZFC','IPRABoundedRhoZFCChecks'];sourceh={n:sha(SRC/(n+'.lean')) for n in names}
w=Path(tempfile.mkdtemp(prefix='ipra-bounded-rho-pinned-'));lib=w/'lib';lib.mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(MANIFEST,w/'package-manifest.jsonl')
for n in names:
 for d in [w/'src/DiophantineConsistency',w/'logs']:shutil.copyfile(SRC/(n+'.lean'),d/(n+'.lean'))
selected={}
for root,dirs,files in os.walk(P/'lib',followlinks=True):
 for f in files:
  if '.olean' in f or f.endswith('.ir'):
   p=Path(root)/f;selected[str(p.relative_to(P/'lib'))]={'path':str(p.resolve()),'sha256':sha(p)}
for rel,v in selected.items():
 out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(v['path'])
(w/'providers.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n');inv_hash=sha(w/'providers.json')
state={'status':'RUNNING','private':str(w),'parent':str(P),'parent_state_sha256':parent_hash,'source_sha256':sourceh,'lean_sha256':lean_hash,'strace_sha256':trace_hash,'provider_inventory_sha256':inv_hash,'provider_objects':len(selected),'package_manifest_sha256':manifest_hash,'package_files':len(package),'scope':'Exact literal bounded-rho native comparison and ZFC client; all actually loaded package object/companion/IR files must belong to a pre/post-hashed manifest. Parent project/Foundation and package source-object ancestry remains inherited historical; no standard-iPRA identification or equation equivalence is asserted.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(LEAN)!=lean_hash or sha(STRACE)!=trace_hash or sha(P/'state.json')!=parent_hash or sha(MANIFEST)!=manifest_hash or sha(w/'package-manifest.jsonl')!=manifest_hash or sha(w/'providers.json')!=inv_hash:return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(v['path'])==v['sha256'] and sha(lib/k)==v['sha256'] for k,v in selected.items()):return False
 if not all(str(Path(v['path']).resolve())==v['resolved'] and sha(v['path'])==v['sha256'] for v in package):return False
 return all(sha(lib/'DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in state.get('records',[]) if r['exit']==0)
def loaded(trace):
 out=set()
 for line in trace.read_text(errors='replace').splitlines():
  if ' = -1 ' in line:continue
  m=re.search(r'open(?:at)?\([^\"]*"([^\"]+)"',line)
  if m:
   p=m.group(1)
   if p.startswith(str(PKG)+'/') and ('.olean' in p or p.endswith('.ir')):out.add(p)
 return out
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=f'{lib}:{PKG}',LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in names:
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();trace=w/'logs'/(n+'.trace');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(STRACE),'-f','-qq','-e','trace=open,openat','-o',str(trace),str(LEAN),'--root='+str(w/'src'),'-M8000','-j1','-DElab.async=false','-o',str(out),str(w/'src/DiophantineConsistency'/(n+'.lean'))];start=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as log:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  actual=loaded(trace);unknown=sorted(actual-package_map.keys());state['records'].append({'name':n,'exit':code,'source_sha256':sourceh[n],'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(w/'logs'/(n+'.log')),'trace_sha256':sha(trace),'loaded_package_files':len(actual),'unknown_package_files':unknown,'seconds':time.monotonic()-start});save();print(n,code,'package',len(actual),'unknown',len(unknown),flush=True);assert code==0 and not unknown
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
