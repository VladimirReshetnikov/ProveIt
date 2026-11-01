#!/usr/bin/env python3
"""Focused native-square replay on one matched historical project provider."""
import hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
D=Path(__file__).resolve().parent;M=D/'manifest.json';SNAP=D/'sources';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean'
SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
raw=M.read_bytes();mh=hashlib.sha256(raw).hexdigest();assert len(sys.argv)==2 and sys.argv[1]==mh
m=json.loads(raw);assert m['status']=='FOCUSED_SQUARE14_DIRECT_NATIVE_INPUT' and H(__file__)==m['driver_sha256'];P=Path(m['parent']);R=Path(m['workspace_root']);SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
assert len(m['order'])==8 and len(set(m['order']))==8

def inventory(root):
 out={}
 for d,_,fs in os.walk(root/'lib',followlinks=True):
  for n in fs:
   if n.endswith(SIDECARS):
    p=Path(d)/n;out[str(p.relative_to(root/'lib'))]={'sha256':H(p),'resolved_path':str(p.resolve())}
 return out
def guards(rows):
 for path,row in rows.items():
  if row is None:assert not os.path.lexists(path),path
  else:assert Path(path).is_file() and str(Path(path).resolve())==row['realpath'] and H(path)==row['sha256'],path
def external():
 assert set(m['parent_external_direct_paths'])==set(m['parent_external_resolved_paths'])
 for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
 assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
 for name,row in m['external'].items():
  rel=name.replace('.', '/')+'.olean';p=next((q for q in (PKG/rel,TOOL/rel) if q.is_file()),None);assert p is not None and str(p.resolve())==row['selected'],name
  guards(row['companions'])
 guards(m['fallback_companions'])
 guards(m['inherited_fallback_companions'])
def frozen():
 assert H(M)==mh and H(__file__)==m['driver_sha256'] and H(D/'prepare.py')==m['preparer_sha256'] and H(LEAN)==m['lean_sha256']
 assert all(str(Path(p).resolve())==p and H(p)==h for p,h in m['gate_guard'].items())
 assert all(str(Path(p).resolve())==p and H(p)==h for p,h in m['origin_guard'].items())
 assert inventory(P)==m['parent_inventory']
 for x in m['model_guards']:guards(x)
 external()
 for n,row in m['sources'].items():
  p=SNAP/'DiophantineConsistency'/(n+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute() and H(p)==row['sha256']
  assert H(SRC/(n+'.lean'))==row['sha256'],('workspace source drift',n)
seen=set();names=set('DiophantineConsistency.'+n for n in m['order'])
for n in m['order']:
 p=SNAP/'DiophantineConsistency'/(n+'.lean');imports=re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M);assert imports==m['sources'][n]['imports'] and all(x not in names or x in seen for x in imports);seen.add('DiophantineConsistency.'+n)
frozen();w=Path(tempfile.mkdtemp(prefix='ipra-square14-direct-native-'));lib=w/'lib';logs=w/'logs';lib.mkdir();logs.mkdir();(w/'manifest.json').write_bytes(raw);(w/'driver.py').write_bytes(Path(__file__).read_bytes())
for rel,row in m['parent_inventory'].items():
 dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(row['resolved_path'])
state={'status':'RUNNING','manifest_sha256':mh,'driver_sha256':m['driver_sha256'],'parent':str(P),'records':[],'boundary':m['boundary']}
def save():(w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')
def scan(stem):
 out={}
 for suffix in SIDECARS:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file();out[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:out[str(p)]=None
 return out
def audit():
 frozen();assert H(w/'manifest.json')==mh and H(w/'driver.py')==m['driver_sha256']
 expected=dict(m['parent_inventory'])
 for row in state['records']:
  if row['exit']==0:
   n=row['module'];obj=lib/'DiophantineConsistency'/(n+'.olean');assert obj.is_file() and not obj.is_symlink() and obj.resolve()==obj.absolute()
   expected['DiophantineConsistency/'+n+'.olean']={'sha256':row['object_sha256'],'resolved_path':str(obj.absolute())};assert H(logs/(n+'.log'))==row['log_sha256'];guards(row['guards'])
 assert inventory(w)==expected
save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in m['order']:
  source=SNAP/'DiophantineConsistency'/(n+'.lean');deps=subprocess.run([str(LEAN),'--deps',str(source)],env=env,capture_output=True,text=True);assert deps.returncode==0 and not deps.stderr,(n,deps.stderr)
  dynamic={};modules=set();direct={}
  for line in deps.stdout.splitlines():
   p=Path(line);assert p.is_absolute() and p.is_file() and str(p).endswith('.olean'),(n,line)
   root=next((r for r in (lib,PKG,TOOL) if p.is_relative_to(r)),None);assert root is not None,(n,line)
   rel=p.relative_to(root);modules.add(str(rel)[:-len('.olean')].replace('/','.'))
   if root==lib:assert str(rel).startswith('DiophantineConsistency/') or str(rel).startswith(('ZFCinPA/','BoundedPAConsistency/')),(n,line)
   direct[str(p)]={'sha256':H(p),'realpath':str(p.resolve())};dynamic.update(scan(Path(str(p)[:-len('.olean')])))
  assert modules-{'Init'}==set(m['sources'][n]['imports'])-{'Init'},(n,modules,m['sources'][n]['imports'])
  guards(dynamic);obj=lib/'DiophantineConsistency'/(n+'.olean');assert not os.path.lexists(obj);obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n+'.log');start=time.monotonic()
  with log.open('x') as out:proc=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(SNAP),str(source),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  text=log.read_text();row={'module':n,'exit':proc.returncode,'source_sha256':H(source),'object_sha256':H(obj) if obj.exists() else None,'log_sha256':H(log),'direct_inputs':direct,'guards':dynamic,'seconds':time.monotonic()-start};state['records'].append(row);save();print(n,proc.returncode,flush=True)
  assert proc.returncode==0 and obj.is_file() and 'error:' not in text and 'sorryAx' not in text and 'warning:' not in text and not re.search(r'\b(?:sorry|admit)\b',text),(n,text)
  if n.endswith('Checks'):
   reports=re.findall(r'depends on axioms: \[([^\]]*)\]',text);expected={'HAExpressionNoZeroEquivChecks':1,'IPRAExpressionNativeChecks':3,'IPRASquareWitnessDirect14NativeChecks':5}[n]
   assert len(reports)==expected and all(set(x.strip() for x in b.split(','))=={'propext','Classical.choice','Quot.sound'} for b in reports),(n,reports)
  guards(dynamic)
 audit();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
 state.update(status='FAILED',failure=repr(exc));save();raise
