#!/usr/bin/env python3
"""Rebuild six literal 14-variable modules on the matched fixed 13-variable peer."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,time
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=D/'manifest.json';F=V/'ipra-frozen-repair-plan-v2/manifest.json';BF=V/'ipra-adaptive-native-fixed-continuation/manifest.json';ORIG=V/'ipra-frozen-repair-plan-v2-verification/receipt.json';CMP=V/'ipra-frozen-repair-v2-verification/receipt.json';AT=CMP.parent/'terminal.json';CMP2=V/'ipra-frozen-repair-v2-verification-fourth/receipt.json';CT=CMP2.parent/'terminal.json';CL=V/'ipra-frozen-repair-plan-v2-closure-audit/receipt.json';SO=V/'ipra-frozen-repair-plan-v2-source-origin-audit/receipt.json';ST=SO.parent/'terminal.json';G=V/'ipra-current-native14-frozen-graph/manifest.json';E=V/'ipra-current-native14-frozen-extra/manifest.json';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';EXTRA=V/'ipra-current-native14-frozen-extra/sources';PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest();dh=h(__file__);assert h(M)==mh and len(sys.argv)==2 and sys.argv[1]==mh and dh==m['driver_sha256'];P=Path(m['peer']);A=Path(m['author']);f=json.loads(BF.read_text());e=json.loads(E.read_text());src=lambda n:(EXTRA if n in m['extra_names'] else SNAP)/(n.replace('.','/')+'.lean')
def inv():
 result={}
 for d,_,fs in os.walk(P/'lib',followlinks=True):
  for name in fs:
   if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
    p=Path(d)/name;result[str(p.relative_to(P/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return result
assert h(P/'state.json')==m['peer_state_sha256'] and h(A/'state.json')==m['author_state_sha256'] and json.loads((P/'state.json').read_text())['status']==json.loads((A/'state.json').read_text())['status']=='PASS'
assert h(F)==m['frozen_13_manifest_sha256'] and h(G)==m['graph_sha256'] and h(E)==m['extra_manifest_sha256'] and h(LEAN)==m['lean_sha256']
assert all(h(src(n))==v for n,v in m['source_sha256'].items()) and inv()==m['parent_inventory']
assert m['order'] and m['order'][-1]=='DiophantineConsistency.IPRACurrentNativeZFCChecks';dirty=set(m['order']);done=set()
for n in m['order']:
 actual=re.findall(r'^import\s+([A-Z][\w.]*)',src(n).read_text(),re.M);assert actual==m['direct_imports'][n];assert all(dep not in dirty or dep in done for dep in actual);done.add(n)
assert all(h(PKG/k)==v['sha256'] and str((PKG/k).resolve())==v['resolved_path'] for k,v in m['external_direct'].items())
w=Path(tempfile.mkdtemp(prefix='ipra-current-native14-fixed-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();(w/'driver.py').write_bytes(Path(__file__).read_bytes());(w/'manifest.json').write_bytes(M.read_bytes())
excluded={n.replace('.','/')+ext for n in m['order'] for ext in ('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')}
for rel in m['parent_inventory']:
 if rel not in excluded:
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to((P/'lib'/rel).resolve())
def drift():
 result=[]
 for n,expected in m['source_sha256'].items():
  if n in f['source_files']:p=R/f['source_files'][n]
  elif n in e['sources'] and e['sources'][n]['workspace_source']:p=R/e['sources'][n]['workspace_source']
  else:continue
  actual=h(p) if p.is_file() else None
  if actual!=expected:result.append({'module':n,'expected':expected,'actual':actual})
 return result
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
 assert h(M)==mh and h(__file__)==dh and h(w/'manifest.json')==mh and h(w/'driver.py')==dh
 assert h(D/'prepare.py')==m['preparer_sha256']
 assert h(P/'state.json')==m['peer_state_sha256'] and h(A/'state.json')==m['author_state_sha256'] and h(F)==m['frozen_13_manifest_sha256'] and h(G)==m['graph_sha256'] and h(E)==m['extra_manifest_sha256'] and h(LEAN)==m['lean_sha256']
 assert h(m['ancestor_state'])==m['ancestor_state_sha256'] and all(h(p)==v for p,v in m['ancestral_manifests'].items())
 assert h(BF)==m['original_fixed_manifest_sha256'] and h(ORIG)==m['parent_origin_receipt_sha256'] and h(CMP)==m['parent_comparison_receipt_sha256'] and h(AT)==m['parent_comparison_author_terminal_sha256'] and h(CMP2)==m['parent_comparison_peer_receipt_sha256'] and h(CT)==m['parent_comparison_terminal_sha256'] and h(CL)==m['parent_closure_receipt_sha256'] and h(SO)==m['parent_source_origin_receipt_sha256'] and h(ST)==m['parent_source_origin_terminal_sha256'] and all(h(p)==v for p,v in m['parent_receipt_checker_guard'].items()) and all(h(p)==v for p,v in m['parent_origin_guard'].items())
 assert all(h(p)==v and str(Path(p).resolve())==m['parent_external_resolved_paths'][p] for p,v in m['parent_external_direct_paths'].items()) and all(not os.path.lexists(p) for p in m['parent_external_absent_paths']) and all(not os.path.lexists(PKG/p) for p in m['parent_external_absent'])
 assert all(h(src(n))==v for n,v in m['source_sha256'].items()) and inv()==m['parent_inventory']
 assert all(h(PKG/k)==v['sha256'] and str((PKG/k).resolve())==v['resolved_path'] for k,v in m['external_direct'].items())
 expected={rel:row for rel,row in m['parent_inventory'].items() if rel not in excluded}
 for row in state['records']:
  if row['exit']==0:
   rel=row['name'].replace('.','/')+'.olean';out=lib/rel;assert out.is_file() and not out.is_symlink() and out.resolve()==out.absolute();expected[rel]={'sha256':row['object_sha256'],'resolved_path':str(out.absolute())};assert h(logs/(row['name'].replace('.','_')+'.log'))==row['log_sha256']
   for dep,x in row['direct_imports'].items():
    path=lib/(dep.replace('.','/')+'.olean');assert path.exists() and str(path.resolve())==x['resolved_path'] and h(path)==x['sha256']
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
 for n in m['order']:
  obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n.replace('.','_')+'.log');direct={};t=time.monotonic()
  for dep in m['direct_imports'][n]:
   path=lib/(dep.replace('.','/')+'.olean');assert path.exists(),str(path);direct[dep]={'sha256':h(path),'resolved_path':str(path.resolve())}
  with log.open('w') as out:r=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(EXTRA),str(src(n)),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  row={'name':n,'exit':r.returncode,'object_sha256':h(obj) if obj.exists() else None,'log_sha256':h(log),'direct_imports':direct,'seconds':time.monotonic()-t};state['records'].append(row);save();print(n,r.returncode,flush=True)
  s=log.read_text();assert r.returncode==0 and 'error:' not in s and 'sorryAx' not in s and not re.search(r'\b(?:sorry|admit)\b',s);row['warnings']=warnings(s);save()
  if n=='DiophantineConsistency.IPRACurrentNativeZFCChecks':
   blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',s);assert len(blocks)==1 and set(x.strip() for x in blocks[0].split(','))=={'propext','Classical.choice','Quot.sound'},(s,blocks)
 audit();state['workspace_drift_after']=drift();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as ex:
 state.update(status='FAILED',failure=repr(ex));save();raise
