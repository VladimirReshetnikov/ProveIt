#!/usr/bin/env python3
"""Compare two completed source-directed eleven-drift replays, not their exit observations."""
from pathlib import Path
import hashlib,json,os,re,shutil,sys
if len(sys.argv)!=4:
 raise SystemExit('usage: compare.py PLAN AUTHOR PEER')
PLAN,A,B=(Path(x).absolute() for x in sys.argv[1:])
assert A.resolve()!=B.resolve() and not os.path.samefile(A/'state.json',B/'state.json'), 'author and peer must be independent runs'
D=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean'
SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
EXT={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
M,DR=PLAN/'manifest.json',PLAN/'replay.py';m,mh=read(M);a,ah=read(A/'state.json');b,bh=read(B/'state.json')
SM=Path(m['candidate_survey_path']);survey,sh=read(SM);SNAP=Path(m['snapshot_root']);P=Path(m['parent_state_path']).parent;R=Path(m['workspace_root']);dh=H(DR);ch=H(__file__)
assert m['status']=='PROVISIONAL_REBASE_INPUT' and sh==m['candidate_survey_sha256']
assert len(survey['sources'])==1099 and len(m['workspace_sources'])==1104
assert len(m['order'])==len(set(m['order']))==351 and m['order']==survey['order'] and m['target']==survey['target']==m['order'][-1]
assert len(m['fallback_companions'])==len(m['order'])*20 and len(m['inherited_fallback_companions'])==3800
expected_fallback={str((root/(name.replace('.', '/')+suffix)).absolute()) for name in m['order'] for root in (PKG,TOOL) for suffix in SIDECARS}
assert set(m['fallback_companions'])==expected_fallback
parent_plan=(R/'Computability/DiophantineConsistency/reviews/ipra-current-repaired-post159-replay-v2/manifest.json').resolve()
assert m['gate_guard'][str(parent_plan)]==H(parent_plan)
parent_manifest=json.loads(parent_plan.read_text());inherited=dict(parent_manifest['inherited_fallback_companions'])
for path,row in parent_manifest['fallback_companions'].items():
 assert path not in inherited or inherited[path]==row
 inherited[path]=row
assert m['inherited_fallback_companions']==inherited
assert a['status']==b['status']=='PASS' and a['manifest_sha256']==b['manifest_sha256']==mh
assert a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256']
assert a['parent_state_sha256']==b['parent_state_sha256']==m['parent_state_sha256']
assert a['survey_manifest_sha256']==b['survey_manifest_sha256']==sh
for state in (a,b):
 for k in ('workspace_drift_before','workspace_drift_after'):assert isinstance(state[k],list)
 assert state['source_matches_workspace_at_final_check']==(not state['workspace_drift_after'])
assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==m['order']
files={}
def add(p,h):
 key=str(Path(p));assert key not in files or files[key]==h,(key,files[key],h);files[key]=h
for path,h in m['gate_guard'].items():assert str(Path(path).resolve())==path;add(path,h)
for path,h in m['origin_guard'].items():assert str(Path(path).resolve())==path;add(path,h)
for path,h in m['parent_external_direct_paths'].items():add(path,h)
add(LEAN,m['lean_sha256']);add(P/'state.json',m['parent_state_sha256']);add(PLAN/'prepare.py',m['preparer_sha256'])
for root in (A,B):add(root/'driver.py',dh);add(root/'manifest.json',mh)
for name,row in survey['sources'].items():
 path=SNAP/(name.replace('.', '/')+'.lean');assert path.is_file() and not path.is_symlink() and path.resolve()==path.absolute();add(path,row['sha256'])
for rel,row in m['parent_inventory'].items():assert str((P/'lib'/rel).resolve())==row['resolved_path'];add(P/'lib'/rel,row['sha256'])
for row in survey['external'].values():
 for path,item in row['companions'].items():
  if item is not None:add(path,item['sha256'])
for group in (m['fallback_companions'],m['inherited_fallback_companions']):
 for path,item in group.items():
  if item is not None:add(path,item['sha256'])

def warnings(text):
 out=[]
 tests=[('unused_simp',r'^This simp argument is unused:'),('unused_section',r'^automatically included section variable\(s\) unused in theorem '),('unused_variable',r'^Variable name `[^`]+` is not explicitly referenced\.$'),('simp_suggestion',r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),('noop_tactic',r"^'.+' tactic does nothing$"),('unreachable_tactic',r'^this tactic is never executed$'),('deprecation',r'^`[^`]+` has been deprecated(?:[.:].*)?$'),('simp_discrimination',r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),('tactic_sequence',r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),('exponent_threshold_notice',r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
 for line in text.splitlines():
  if 'warning:' not in line:continue
  msg=line.split('warning:',1)[1].strip();hits=[cat for cat,pat in tests if re.search(pat,msg)]
  assert len(hits)==1,('unrecognized warning',line);out.append({'category':hits[0],'message':msg,'full_line':line})
 return out

dirty=set(m['order']);seen=set()
for name in m['order']:
 actual=re.findall(r'^import\s+([A-Z][\w.]*)',(SNAP/(name.replace('.', '/')+'.lean')).read_text(),re.M)
 assert actual==survey['sources'][name]['imports'] and all(dep not in dirty or dep in seen for dep in actual);seen.add(name)
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ('name','exit','object_sha256','log_sha256','warnings')) and x['exit']==y['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
 for root,row in ((A,x),(B,y)):
  name=row['name'];assert set(row['direct_imports'])==set(survey['sources'][name]['imports'])
  add(root/'lib'/(name.replace('.', '/')+'.olean'),row['object_sha256']);log=root/'logs'/(name.replace('.', '_')+'.log');add(log,row['log_sha256'])
  text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text) and warnings(text)==row['warnings']
  if name==m['target']:
   reports=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
   assert len(reports)==2 and all(set(q.strip() for q in block.split(','))=={'propext','Classical.choice','Quot.sound'} for block in reports)
  for dep,info in row['direct_imports'].items():
   path=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else root/'lib'/(dep.replace('.', '/')+'.olean')
   assert path.exists() and str(path.resolve())==info['resolved_path'] and H(path)==info['sha256'];add(info['resolved_path'],info['sha256'])
excluded={name.replace('.', '/')+suffix for name in dirty for suffix in SIDECARS}
def expected(root,state):
 out={rel:row for rel,row in m['parent_inventory'].items() if rel not in excluded}
 for row in state['records']:
  rel=row['name'].replace('.', '/')+'.olean';path=root/'lib'/rel
  assert path.is_file() and not path.is_symlink() and path.resolve()==path.absolute()
  out[rel]={'sha256':row['object_sha256'],'resolved_path':str(path.absolute())}
 return out
def inventory(root):
 out={}
 for d,_,names in os.walk(root/'lib',followlinks=True):
  for name in names:
   if name.endswith(SIDECARS):
    p=Path(d)/name;out[str(p.relative_to(root/'lib'))]={'sha256':H(p),'resolved_path':str(p.resolve())}
 return out
expa,expb=expected(A,a),expected(B,b)
def external():
 assert set(m['parent_external_direct_paths'])==set(m['parent_external_resolved_paths'])
 assert all(str(Path(path).resolve())==v for path,v in m['parent_external_resolved_paths'].items())
 assert all(not os.path.lexists(path) for path in m['parent_external_absent_paths'])
 for name,row in survey['external'].items():
  rel=name.replace('.', '/')+'.olean';p=next((q for q in (PKG/rel,TOOL/rel) if q.is_file()),None)
  assert p is not None and str(p.resolve())==row['selected']
  for path,item in row['companions'].items():
   if item is None:assert not os.path.lexists(path)
   else:assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256']
 for group in (m['fallback_companions'],m['inherited_fallback_companions']):
  for path,item in group.items():
   if item is None:assert not os.path.lexists(path)
   else:assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256']
def audit():
 assert H(M)==mh and H(SM)==sh and H(DR)==dh and H(__file__)==ch and H(A/'state.json')==ah and H(B/'state.json')==bh
 assert all(H(path)==h for path,h in files.items())
 assert all(str(Path(path).resolve())==path for path in m['gate_guard']) and all(str(Path(path).resolve())==path for path in m['origin_guard'])
 assert all((p:=SNAP/(n.replace('.', '/')+'.lean')).is_file() and not p.is_symlink() and p.resolve()==p.absolute() for n in survey['sources'])
 assert all(str((P/'lib'/rel).resolve())==row['resolved_path'] for rel,row in m['parent_inventory'].items())
 external();assert inventory(A)==expa and inventory(B)==expb
 for root,state in ((A,a),(B,b)):
  for row in state['records']:
   for dep,info in row['direct_imports'].items():
    path=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else root/'lib'/(dep.replace('.', '/')+'.olean')
    assert path.exists() and str(path.resolve())==info['resolved_path'] and H(path)==info['sha256']
def drift():
 out=[]
 for name,row in m['workspace_sources'].items():
  path=R/row['path']
  try:actual=H(path) if path.is_file() else None
  except OSError:actual=None
  if actual!=row['sha256']:out.append({'module':name,'expected':row['sha256'],'actual':actual})
 return out

audit()
for reserved in ('receipt.json','author-state.json','independent-state.json','author-logs','independent-logs'):
 assert not os.path.lexists(D/reserved),('refusing to overwrite evidence',reserved)
for root,label,state_sha in ((A,'author',ah),(B,'independent',bh)):
 dest=D/(label+'-logs');dest.mkdir();shutil.copyfile(root/'state.json',D/(label+'-state.json'));assert H(D/(label+'-state.json'))==state_sha
 for row in a['records']:
  name=row['name'].replace('.', '_')+'.log';shutil.copyfile(root/'logs'/name,dest/name);assert H(dest/name)==row['log_sha256']
audit();now=drift();audit();now_confirm=drift()
current=not now and not now_confirm and all(not run[k] for run in (a,b) for k in ('workspace_drift_before','workspace_drift_after'))
result={'status':'MATCHED_PASS','author_path':str(A),'peer_path':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,
 'manifest_sha256':mh,'survey_manifest_sha256':sh,'driver_sha256':dh,'compare_sha256':ch,'rows':len(a['records']),
 'matched_rows':[{'name':row['name'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'warnings':row['warnings']} for row in a['records']],
 'guarded_file_count':len(files),'workspace_drift':{'author_before':a['workspace_drift_before'],'author_after':a['workspace_drift_after'],
 'peer_before':b['workspace_drift_before'],'peer_after':b['workspace_drift_after'],'comparison_final':now,'comparison_final_confirm':now_confirm},
 'workspace_matches_snapshot_through_observations':current,'boundary':m['boundary']}
with (D/'receipt.json').open('x') as out:json.dump(result,out,sort_keys=True,indent=2);out.write('\n')
print('MATCHED_PASS',len(a['records']),'rows',len(files),'files','workspace_matches',current)
