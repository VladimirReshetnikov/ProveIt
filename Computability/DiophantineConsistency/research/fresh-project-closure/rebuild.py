#!/usr/bin/env python3
"""Rebuild a frozen declared project closure from scratch; package ancestry remains inherited."""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
p=argparse.ArgumentParser();p.add_argument('--snapshot',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--provider-receipt',type=Path,required=True);p.add_argument('--snapshot-sha256',required=True);p.add_argument('--provider-sha256',required=True);p.add_argument('--foundation-input',type=Path,required=True);p.add_argument('--expected-axiom-reports',type=int,required=True);p.add_argument('--lean',type=Path,default=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'));a=p.parse_args()
snap=a.snapshot.resolve(strict=True);manifest=snap/'manifest.json';m=json.loads(manifest.read_text());assert m['status']=='FROZEN_NOT_COMPILED'
provider=a.provider_receipt.resolve(strict=True);assert H(manifest)==a.snapshot_sha256 and H(provider)==a.provider_sha256;pr=json.loads(provider.read_text());foundation_input=a.foundation_input.resolve(strict=True);assert H(foundation_input)==pr['manifest_sha256'];fi=json.loads(foundation_input.read_text());assert pr['status']=='BUILT' and pr['exit_code']==0 and pr.get('declared_external_guard') is not None
pkg=Path(pr['overlay']).absolute();foundation=Path(pr['root']).resolve()/'.lake/build/lib/lean/Foundation';assert (pkg/'Foundation').resolve(strict=True)==foundation
lean=a.lean.resolve(strict=True);assert H(lean)==fi['lean_sha256'];tool=lean.parent.parent/'lib/lean';root=Path(m['root']);names=m['order'];sources=m['sources'];assert len(names)==len(sources)==m['project_modules'] and names[-1]==m['target'] and len(set(names))==len(names)
output=a.output.absolute();output.mkdir(parents=True,exist_ok=False);lib=output/'lib';lib.mkdir();logs=output/'logs';logs.mkdir();statepath=output/'state.json'
state={'status':'RUNNING','phase':'preflight','snapshot':str(snap),'manifest_sha256':H(manifest),'provider_receipt_sha256':H(provider),'provider':str(provider),'package_overlay':str(pkg),'lean_sha256':H(lean),'lean_path':str(lean),'driver_sha256':H(Path(__file__)),'foundation_input_sha256':H(foundation_input),'foundation_input_path':str(foundation_input),'expected_axiom_reports':a.expected_axiom_reports,'records':[],'scope':'Fresh compilation from frozen source-declared project closure, no prior project objects. Foundation from one guarded replacement provider. Package-transitive and dynamic imports, executable/toolchain dependencies and transient mutation between observations remain outside this receipt.'}
def save():
 tmp=output/'state.tmp';tmp.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');tmp.replace(statepath)
def check_guard(g):
 for path,expected in g.items():
  q=Path(path)
  if expected is None:
   if os.path.lexists(q):raise ValueError(('unexpected file',path))
  elif not q.is_file() or str(q.resolve())!=expected['realpath'] or H(q)!=expected['sha256']:raise ValueError(('changed input',path))
def scan(stem):
 d={}
 for suffix in SUFFIXES:
  q=Path(str(stem)+suffix)
  if os.path.lexists(q):
   if not q.is_file():raise ValueError(('broken companion',str(q)))
   d[str(q)]={'realpath':str(q.resolve()),'sha256':H(q)}
  else:d[str(q)]=None
 return d
def verify_snapshot():
 if H(manifest)!=state['manifest_sha256']:raise ValueError('manifest changed')
 for name in names:
  row=sources[name];q=snap/row['snapshot_path']; expected=snap/'src'/(name.replace('.','/')+'.lean')
  if q != expected or not q.resolve().is_relative_to(snap/'src') or not q.is_file() or q.is_symlink() or (snap/'src').is_symlink():raise ValueError(('snapshot path',name))
  for parent in q.relative_to(snap/'src').parents:
   if (snap/'src'/parent).is_symlink():raise ValueError(('snapshot symlinked parent',name))
  if H(q)!=row['sha256']:raise ValueError(('snapshot drift',name))
def verify_provider():
 if H(provider)!=state['provider_receipt_sha256']:raise ValueError('provider receipt changed')
 check_guard(pr['declared_external_guard'])
 for rel,expected in pr['foundation_artifacts'].items():
  q=foundation/rel
  if not q.is_file() or q.is_symlink() or H(q)!=expected:raise ValueError(('Foundation artifact drift',rel))
 # Guard unexpected Foundation artifacts as well as each inventoried file.
 actual={str(q.relative_to(foundation)) for q in foundation.rglob('*') if q.is_file() or q.is_symlink()}
 if actual!=set(pr['foundation_artifacts']):raise ValueError('Foundation inventory changed')
project_tops={name.split('.')[0] for name in names}
def reject_project_fallbacks():
 # No project namespace in either fallback, including direct files and libraries.
 for rootdir in (pkg,tool):
  for top in project_tops:
   for suffix in ('',*SUFFIXES,'.so','.dll','.dylib'):
    if os.path.lexists(rootdir/(top+suffix)):raise ValueError(('project fallback artifact',str(rootdir/(top+suffix))))
# This admits only paths whose logical resolution is anchored in the fresh
# project root, the validated package-only overlay, or the Lean toolchain.
def logical_name(path,base):
 rel=path.relative_to(base)
 if not str(rel).endswith('.olean'):raise ValueError(('not olean',str(path)))
 return str(rel)[:-6].replace('/','.')
env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1');
for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(var,None)
save();guard={};fresh={}
try:
 verify_snapshot();verify_provider();reject_project_fallbacks()
 if any(lib.iterdir()):raise ValueError('project output not empty')
 for idx,name in enumerate(names):
  state.update(phase='compile',module=name,index=idx);save()
  row=sources[name];source=snap/row['snapshot_path']
  if H(source)!=row['sha256']:raise ValueError(('source before',name))
  dep=subprocess.run([str(lean),'--deps',str(source)],env=env,capture_output=True,text=True)
  if dep.returncode or dep.stderr:raise ValueError(('deps failure',name,dep.returncode,dep.stderr))
  observed={};direct={}
  for line in dep.stdout.splitlines():
   q=Path(line)
   if not q.is_absolute() or not q.is_file():raise ValueError(('unavailable dependency',name,line))
   if q.is_relative_to(lib):
    module=logical_name(q,lib)
    if module not in fresh:raise ValueError(('project dependency not freshly built',name,module))
    check_guard(fresh[module]);kind='project'
   elif q.is_relative_to(pkg):
    module=logical_name(q,pkg);kind='package'
    if module.split('.')[0] in project_tops:raise ValueError(('project dependency fell back',name,module))
    if module.startswith('Foundation.') and not q.resolve().is_relative_to(foundation):raise ValueError(('mixed Foundation provider',module))
   elif q.is_relative_to(tool):module=logical_name(q,tool);kind='toolchain'
   else:raise ValueError(('dependency outside allowed roots',name,line))
   if module.split('.')[0]=='Foundation' and (kind!='package' or not q.resolve().is_relative_to(foundation)):raise ValueError(('Foundation outside fresh provider',module))
   if module in observed and observed[module]!=str(q):raise ValueError(('duplicate module provider',module))
   observed[module]=str(q);direct[module]={'path':str(q),'kind':kind,'sha256':H(q)}
   for key,value in scan(Path(str(q)[:-6])).items():
    if key in guard and guard[key]!=value:raise ValueError(('companion drift',key))
    guard[key]=value
  declared=set(row['imports']);actual=set(observed)
  if not declared<=actual or actual-declared-{'Init'}:raise ValueError(('declared and compiler deps disagree',name,sorted(declared-actual),sorted(actual-declared-{'Init'})))
  project_declared={x for x in declared if x in sources}
  if {x for x,v in direct.items() if v['kind']=='project'}!=project_declared:raise ValueError(('project deps mismatch',name))
  inputs={k:v for k,v in guard.items() if any(k.startswith(str(Path(x['path']) )[:-6]+'.') for x in direct.values())};check_guard(inputs)
  obj=lib/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  if os.path.lexists(obj):raise ValueError(('output preexists',name))
  log=logs/(f'{idx:04d}-'+name.replace('.','_')+'.log')
  cmd=[str(lean),'-M8000','-j1','-DElab.async=false','--root='+str(snap/'src'),str(source),'-o',str(obj)]
  t=time.monotonic()
  with log.open('x') as f:proc=subprocess.run(cmd,cwd=snap/'src',env=env,stdout=f,stderr=subprocess.STDOUT)
  text=log.read_text();reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
  rec={'module':name,'exit':proc.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':H(source),'direct_inputs':direct,'log':str(log),'log_sha256':H(log),'object_sha256':H(obj) if obj.is_file() else None,'axiom_reports':reports};state['records'].append(rec);save()
  if proc.returncode or not obj.is_file() or re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text):raise ValueError(('compilation failed',name))
  if name==m['target']:
   if len(reports)!=a.expected_axiom_reports:raise ValueError(('unexpected endpoint axiom report count',len(reports),a.expected_axiom_reports))
   for rep in reports:
    if {x.strip() for x in rep.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:raise ValueError(('unexpected endpoint axiom',rep))
  if H(source)!=row['sha256']:raise ValueError(('source after',name))
  check_guard(inputs)
  if obj.is_symlink():raise ValueError(('project output symlink',name))
  fresh[name]=scan(Path(str(obj)[:-6]));print('PASS',idx+1,len(names),name,flush=True)
 state.update(phase='final authentication',module=None);save();verify_snapshot();verify_provider();reject_project_fallbacks();check_guard(guard)
 for name,g in fresh.items():check_guard(g)
 for r in state['records']:
  if H(r['log'])!=r['log_sha256']:raise ValueError(('log changed',r['module']))
 if H(lean)!=state['lean_sha256'] or H(Path(__file__))!=state['driver_sha256'] or H(foundation_input)!=state['foundation_input_sha256'] or H(provider)!=state['provider_receipt_sha256']:raise ValueError('compiler or provider changed')
 drift=[name for name in names if not (root/sources[name]['workspace_path']).is_file() or H(root/sources[name]['workspace_path'])!=sources[name]['sha256']]
 state.update(status='PASS',phase='complete',workspace_source_drift=drift,source_status='CURRENT_AT_FINAL_CHECK' if not drift else 'HISTORICAL_SNAPSHOT',guarded_companions=guard,outputs=fresh);save();print('PASS',len(names),'workspace_source_drift',len(drift),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
