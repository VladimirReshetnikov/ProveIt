#!/usr/bin/env python3
"""Independently replay a fixed-snapshot provenance-repair plan."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,time
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=D/'manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest();dh=h(__file__);assert len(sys.argv)==2 and sys.argv[1]==mh and h(M)==mh and dh==m['driver_sha256'];f=json.loads(F.read_text());P=Path(m['peer_state_path']).parent;A=Path(m['author_state_path']).parent
assert h(F)==m['fixed_manifest_sha256'] and h(LEAN)==m['lean_sha256'];assert h(P/'state.json')==m['peer_state_sha256'] and h(A/'state.json')==m['author_state_sha256'];assert json.loads((P/'state.json').read_text())['status']==json.loads((A/'state.json').read_text())['status']=='PASS';assert m['source_sha256']==f['source_sha256']
def inventory():
 out={}
 for d,_,fs in os.walk(P/'lib',followlinks=True):
  for name in fs:
   if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
    p=Path(d)/name;out[str(p.relative_to(P/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return out
def immutable_audit():
 assert h(M)==mh and h(__file__)==dh and h(F)==m['fixed_manifest_sha256'] and h(LEAN)==m['lean_sha256'];assert h(P/'state.json')==m['peer_state_sha256'] and h(A/'state.json')==m['author_state_sha256']
 assert all(h(SNAP/(n.replace('.','/')+'.lean'))==v for n,v in m['source_sha256'].items());assert inventory()==m['parent_inventory'];assert all(h(path)==v for path,v in m['origin_guard'].items())
 assert all(h(PKG/rel)==v['sha256'] and str((PKG/rel).resolve())==v['resolved_path'] for rel,v in m['external_files'].items());assert all(not os.path.lexists(PKG/rel) for rel in m['external_absent']);assert all(h(path)==v for path,v in m['external_direct_paths'].items()) and all(str(Path(path).resolve())==v for path,v in m['external_resolved_paths'].items()) and all(not os.path.lexists(path) for path in m['external_absent_paths'])
 for n,x in m['external_lookup'].items():
  rel=Path(n.replace('.','/')+'.olean');candidates=[PKG/rel,LEAN.parent.parent/'lib/lean'/rel];selected=next((p for p in candidates if p.exists()),None);assert selected is not None and str(selected.resolve())==x['resolved_path'] and h(selected)==x['sha256']
immutable_audit();assert m['order'] and m['order'][-1]=='DiophantineConsistency.IPRAAdaptiveNativeZFCChecks';dirty=set(m['order']);seen=set();ext={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
for n in m['order']:
 actual=re.findall(r'^import\s+([A-Z][\w.]*)',(SNAP/(n.replace('.','/')+'.lean')).read_text(),re.M);assert actual==m['direct_imports'][n];assert all(dep not in dirty or dep in seen for dep in actual);seen.add(n)
w=Path(tempfile.mkdtemp(prefix='ipra-frozen-ancestry-repair-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();(w/'driver.py').write_bytes(Path(__file__).read_bytes());(w/'manifest.json').write_bytes(raw)
excluded={n.replace('.','/')+s for n in dirty for s in ['.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash']}
for rel,row in m['parent_inventory'].items():
 if rel not in excluded:
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to((P/'lib'/rel).resolve())
def drift():
 out=[]
 for n,p in f['source_files'].items():
  path=R/p;actual=h(path) if path.is_file() else None;expected=m['source_sha256'][n]
  if actual!=expected:out.append({'module':n,'expected':expected,'actual':actual})
 return out
state={'status':'RUNNING','manifest_sha256':mh,'driver_sha256':dh,'parent_state_sha256':m['peer_state_sha256'],'records':[],'workspace_drift_before':drift(),'boundary':m['boundary']}
def save():(w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')
def overlay_inventory():
 result={}
 for d,_,fs in os.walk(lib,followlinks=True):
  for name in fs:
   if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
    p=Path(d)/name;result[str(p.relative_to(lib))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return result
def audit():
 immutable_audit();assert h(w/'manifest.json')==mh and h(w/'driver.py')==dh
 expected={rel:x for rel,x in m['parent_inventory'].items() if rel not in excluded}
 for row in state['records']:
  if row['exit']==0:
   rel=row['name'].replace('.','/')+'.olean';out=lib/rel;assert out.is_file() and not out.is_symlink() and out.resolve()==out.absolute();expected[rel]={'sha256':row['object_sha256'],'resolved_path':str(out.absolute())};assert h(logs/(row['name'].replace('.','_')+'.log'))==row['log_sha256']
 assert overlay_inventory()==expected
 for row in state['records']:
  for dep,x in row['direct_imports'].items():
   path=Path(m['external_lookup'][dep]['resolved_path']) if dep.split('.')[0] in ext else lib/(dep.replace('.','/')+'.olean')
   assert path.exists() and str(path.resolve())==x['resolved_path'] and h(path)==x['sha256']

def warnings(s):
 out=[]
 for line in s.splitlines():
  if 'warning:' not in line: continue
  msg=line.split('warning:',1)[1].strip()
  tests=[('unused_simp',r'^This simp argument is unused:'),('unused_section',r'^automatically included section variable\(s\) unused in theorem '),('unused_variable',r'^Variable name `[^`]+` is not explicitly referenced\.$'),('simp_suggestion',r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),('noop_tactic',r"^'.+' tactic does nothing$"),('unreachable_tactic',r'^this tactic is never executed$'),('deprecation',r'^`[^`]+` has been deprecated(?:[.:].*)?$'),('simp_discrimination',r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),('tactic_sequence',r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),('exponent_threshold_notice',r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
  hits=[cat for cat,pat in tests if re.search(pat,msg)]
  assert len(hits)==1,('unrecognized warning',line)
  out.append({'category':hits[0],'message':msg,'full_line':line})
 return out

save();print('PRIVATE',w,flush=True)
try:
 audit();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in m['order']:
  obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n.replace('.','_')+'.log');direct={};t=time.monotonic()
  for dep in m['direct_imports'][n]:
   rel=Path(dep.replace('.','/')+'.olean')
   if dep.split('.')[0] in ext:path=Path(m['external_lookup'][dep]['resolved_path'])
   else:path=lib/rel
   assert path.exists(),str(path);direct[dep]={'sha256':h(path),'resolved_path':str(path.resolve())}
  with log.open('w') as out:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(SNAP),str(SNAP/(n.replace('.','/')+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  row={'name':n,'exit':r.returncode,'object_sha256':h(obj) if obj.exists() else None,'log_sha256':h(log),'direct_imports':direct,'seconds':time.monotonic()-t};state['records'].append(row);save();print(n,r.returncode,flush=True)
  s=log.read_text();assert r.returncode==0 and 'error:' not in s and 'sorryAx' not in s and not re.search(r'\b(?:sorry|admit)\b',s);row['warnings']=warnings(s);save()
  if n=='DiophantineConsistency.IPRAAdaptiveNativeZFCChecks':
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',s);assert len(blocks)==2 and all(set(x.strip() for x in b.split(','))=={'propext','Classical.choice','Quot.sound'} for b in blocks),(s,blocks)
 audit();state['workspace_drift_after']=drift();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as ex:
 state.update(status='FAILED',failure=repr(ex));save();raise
