#!/usr/bin/env python3
"""Rebuild the surveyed source snapshot on the repaired fixed-source parent."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,time
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=D/'manifest.json';SUR=V/'ipra-current-repaired-survey';SM=SUR/'manifest.json';SNAP=SUR/'sources';PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest();dh=h(__file__);assert len(sys.argv)==2 and sys.argv[1]==mh and h(M)==mh and dh==m['driver_sha256'];sraw=SM.read_bytes();survey=json.loads(sraw);assert hashlib.sha256(sraw).hexdigest()==m['survey_manifest_sha256'];P=Path(m['parent_state_path']).parent;assert survey['parent']==str(P) and survey['parent_state_sha256']==m['parent_state_sha256'];assert h(P/'state.json')==m['parent_state_sha256'] and json.loads((P/'state.json').read_text())['status']=='PASS';assert h(LEAN)==m['lean_sha256']
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash');EXT={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
def inventory():
 out={}
 for d,_,fs in os.walk(P/'lib',followlinks=True):
  for name in fs:
   if name.endswith(SUFFIXES):
    p=Path(d)/name;out[str(p.relative_to(P/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return out
def external_audit():
 for n,row in survey['external'].items():
  rel=Path(n.replace('.','/')+'.olean');pick=next((p for p in [PKG/rel,TOOL/rel] if p.is_file()),None);assert pick is not None and str(pick.resolve())==row['selected'],n
  for path,v in row['companions'].items():
   if v is None:assert not os.path.lexists(path),path
   else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and h(path)==v['sha256'],path
def frozen_audit():
 assert h(M)==mh and h(__file__)==dh and h(SM)==m['survey_manifest_sha256'] and h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256'] and h(D/'prepare.py')==m['preparer_sha256']
 assert all(h(p)==v and str(Path(p).resolve())==p for p,v in m['gate_guard'].items());assert all(h(p)==v and str(Path(p).resolve())==p for p,v in m['origin_guard'].items());assert all(h(p)==v for p,v in m['parent_external_direct_paths'].items()) and all(str(Path(p).resolve())==v for p,v in m['parent_external_resolved_paths'].items()) and all(not os.path.lexists(p) for p in m['parent_external_absent_paths']);assert all((p:=SNAP/(n.replace('.','/')+'.lean')).is_file() and not p.is_symlink() and p.resolve()==p.absolute() and h(p)==v['sha256'] for n,v in survey['sources'].items());assert inventory()==m['parent_inventory'];external_audit()
 for n,row in survey['selected_project_objects'].items():
  p=P/'lib'/(n.replace('.','/')+'.olean');assert p.is_file() and str(p.resolve())==row['path'] and h(p)==row['sha256'],n
assert len(survey['sources'])==1099 and len(survey['order'])==258 and len(survey['external'])==106 and survey['order'][-1]==survey['target'];dirty=set(survey['order']);seen=set()
for n in survey['order']:
 actual=re.findall(r'^import\s+([A-Z][\w.]*)',(SNAP/(n.replace('.','/')+'.lean')).read_text(),re.M);assert actual==survey['sources'][n]['imports'];assert all(x not in dirty or x in seen for x in actual);seen.add(n)
assert all(n in survey['selected_project_objects'] or n in dirty for n in survey['sources'])
frozen_audit();w=Path(tempfile.mkdtemp(prefix='ipra-current-repaired-build-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();(w/'driver.py').write_bytes(Path(__file__).read_bytes());(w/'manifest.json').write_bytes(raw)
excluded={n.replace('.','/')+x for n in dirty for x in SUFFIXES}
for rel,row in m['parent_inventory'].items():
 if rel not in excluded:
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to((P/'lib'/rel).resolve())
def drift():
 out=[]
 for n,row in survey['sources'].items():
  p=R/row['path']
  try:actual=h(p) if p.is_file() else None
  except OSError:actual=None
  if actual!=row['sha256']:out.append({'module':n,'expected':row['sha256'],'actual':actual})
 return out
state={'status':'RUNNING','manifest_sha256':mh,'survey_manifest_sha256':m['survey_manifest_sha256'],'driver_sha256':dh,'parent_state_sha256':m['parent_state_sha256'],'records':[],'workspace_drift_before':drift(),'boundary':m['boundary']}
def save():(w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')
def overlay_inventory():
 out={}
 for d,_,fs in os.walk(lib,followlinks=True):
  for name in fs:
   if name.endswith(SUFFIXES):
    p=Path(d)/name;out[str(p.relative_to(lib))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return out
def audit():
 frozen_audit();assert h(w/'manifest.json')==mh and h(w/'driver.py')==dh
 expected={rel:row for rel,row in m['parent_inventory'].items() if rel not in excluded}
 for row in state['records']:
  if row['exit']==0:
   rel=row['name'].replace('.','/')+'.olean';p=lib/rel;assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();expected[rel]={'sha256':row['object_sha256'],'resolved_path':str(p.absolute())};assert h(logs/(row['name'].replace('.','_')+'.log'))==row['log_sha256']
   for dep,x in row['direct_imports'].items():
    p=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else lib/(dep.replace('.','/')+'.olean');assert p.exists() and str(p.resolve())==x['resolved_path'] and h(p)==x['sha256']
 assert overlay_inventory()==expected

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
 for n in survey['order']:
  obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n.replace('.','_')+'.log');direct={};t=time.monotonic()
  for dep in survey['sources'][n]['imports']:
   p=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else lib/(dep.replace('.','/')+'.olean');assert p.exists(),str(p);direct[dep]={'sha256':h(p),'resolved_path':str(p.resolve())}
  with log.open('w') as out:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(SNAP),str(SNAP/(n.replace('.','/')+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  row={'name':n,'exit':r.returncode,'object_sha256':h(obj) if obj.exists() else None,'log_sha256':h(log),'direct_imports':direct,'seconds':time.monotonic()-t};state['records'].append(row);save();print(n,r.returncode,flush=True)
  text=log.read_text();assert r.returncode==0 and 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text);row['warnings']=warnings(text);save()
  if n==survey['target']:
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',text);assert len(blocks)==2 and all(set(x.strip() for x in block.split(','))=={'propext','Classical.choice','Quot.sound'} for block in blocks),(text,blocks)
 audit();state['workspace_drift_after']=drift();state['source_matches_workspace_at_final_check']=not state['workspace_drift_after'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as ex:
 state.update(status='FAILED',failure=repr(ex));save();raise
