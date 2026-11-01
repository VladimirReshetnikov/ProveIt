#!/usr/bin/env python3
"""Compare two completed 258-module source-survey replays."""
from pathlib import Path
import hashlib,json,os,re,shutil,sys
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';SUR=V/'ipra-current-repaired-survey';SM=SUR/'manifest.json';SNAP=SUR/'sources';PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==4;PLAN=Path(sys.argv[1]);A=Path(sys.argv[2]);B=Path(sys.argv[3]);assert A.resolve()!=B.resolve() and not os.path.samefile(A/'state.json',B/'state.json'), 'author and peer must be independent runs';M=PLAN/'manifest.json';DR=PLAN/'replay.py';m,mh=read(M);s,sh=read(SM);a,ah=read(A/'state.json');b,bh=read(B/'state.json');dh=h(DR);ch=h(__file__);assert sh==m['survey_manifest_sha256'] and a['status']==b['status']=='PASS' and a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256'];assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==s['order'];P=Path(m['parent_state_path']).parent;EXT={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'};SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
files={}
def add(p,v):
 k=str(Path(p));assert k not in files or files[k]==v,(k,files[k],v);files[k]=v
for p,v in m['gate_guard'].items():assert str(Path(p).resolve())==p;add(p,v)
for p,v in m['origin_guard'].items():assert str(Path(p).resolve())==p;add(p,v)
for p,v in m['parent_external_direct_paths'].items():add(p,v)
add(LEAN,m['lean_sha256']);add(P/'state.json',m['parent_state_sha256']);add(PLAN/'prepare.py',m['preparer_sha256'])
for root in [A,B]:add(root/'driver.py',dh);add(root/'manifest.json',mh)
for n,v in s['sources'].items():
 p=SNAP/(n.replace('.','/')+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();add(p,v['sha256'])
for rel,v in m['parent_inventory'].items():assert str((P/'lib'/rel).resolve())==v['resolved_path'];add(P/'lib'/rel,v['sha256'])
for n,v in s['external'].items():
 for path,item in v['companions'].items():
  if item is not None:add(path,item['sha256'])

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

dirty=set(s['order']);done=set()
for n in s['order']:
 actual=re.findall(r'^import\s+([A-Z][\w.]*)',(SNAP/(n.replace('.','/')+'.lean')).read_text(),re.M);assert actual==s['sources'][n]['imports'] and all(x not in dirty or x in done for x in actual);done.add(n)
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ['name','exit','object_sha256','log_sha256','warnings']) and x['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
 for root,row in [(A,x),(B,y)]:
  n=row['name'];assert set(row['direct_imports'])==set(s['sources'][n]['imports']);add(root/'lib'/(n.replace('.','/')+'.olean'),row['object_sha256']);log=root/'logs'/(n.replace('.','_')+'.log');add(log,row['log_sha256']);text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text) and warnings(text)==row['warnings']
  for dep,v in row['direct_imports'].items():
   path=Path(s['external'][dep]['selected']) if dep.split('.')[0] in EXT else root/'lib'/(dep.replace('.','/')+'.olean');assert path.exists() and str(path.resolve())==v['resolved_path'] and h(path)==v['sha256'];add(v['resolved_path'],v['sha256'])
excluded={n.replace('.','/')+x for n in dirty for x in SUFFIXES}
def expected(root,state):
 out={rel:v for rel,v in m['parent_inventory'].items() if rel not in excluded}
 for r in state['records']:
  rel=r['name'].replace('.','/')+'.olean';p=root/'lib'/rel;assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();out[rel]={'sha256':r['object_sha256'],'resolved_path':str(p.absolute())}
 return out
def inventory(root):
 out={}
 for d,_,fs in os.walk(root/'lib',followlinks=True):
  for name in fs:
   if name.endswith(SUFFIXES):
    p=Path(d)/name;out[str(p.relative_to(root/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return out
expa=expected(A,a);expb=expected(B,b)
def externals():
 for n,row in s['external'].items():
  rel=Path(n.replace('.','/')+'.olean');p=next((q for q in [PKG/rel,TOOL/rel] if q.is_file()),None);assert p is not None and str(p.resolve())==row['selected']
  for path,v in row['companions'].items():
   if v is None:assert not os.path.lexists(path)
   else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and h(path)==v['sha256']
def audit():
 assert h(M)==mh and h(SM)==sh and h(DR)==dh and h(__file__)==ch and h(A/'state.json')==ah and h(B/'state.json')==bh
 assert all(h(p)==v for p,v in files.items());assert all(str(Path(p).resolve())==p for p in m['gate_guard']) and all(str(Path(p).resolve())==p for p in m['origin_guard']);assert all((p:=SNAP/(n.replace('.','/')+'.lean')).is_file() and not p.is_symlink() and p.resolve()==p.absolute() for n in s['sources']);assert all(str((P/'lib'/rel).resolve())==v['resolved_path'] for rel,v in m['parent_inventory'].items());assert all(str(Path(p).resolve())==v for p,v in m['parent_external_resolved_paths'].items()) and all(not os.path.lexists(p) for p in m['parent_external_absent_paths']);externals();assert inventory(A)==expa and inventory(B)==expb
 for root,state in [(A,a),(B,b)]:
  for row in state['records']:
   for dep,v in row['direct_imports'].items():
    p=Path(s['external'][dep]['selected']) if dep.split('.')[0] in EXT else root/'lib'/(dep.replace('.','/')+'.olean');assert p.exists() and str(p.resolve())==v['resolved_path'] and h(p)==v['sha256']
def workspace_drift():
 out=[]
 for n,row in s['sources'].items():
  p=R/row['path']
  try:actual=h(p) if p.is_file() else None
  except OSError:actual=None
  if actual!=row['sha256']:out.append({'module':n,'expected':row['sha256'],'actual':actual})
 return out
audit()
for reserved in ['receipt.json','author-state.json','independent-state.json','author-logs','independent-logs']:
 assert not (D/reserved).exists(),('refusing to overwrite comparison evidence',reserved)
for root,label,expected_sha in [(A,'author',ah),(B,'independent',bh)]:
 dest=D/(label+'-logs');dest.mkdir();shutil.copyfile(root/'state.json',D/(label+'-state.json'));assert h(D/(label+'-state.json'))==expected_sha
 for row in a['records']:
  name=row['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/name,dest/name);assert h(dest/name)==row['log_sha256']
log=(A/'logs'/(s['target'].replace('.','_')+'.log')).read_text();blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',log);assert len(blocks)==2 and all(set(x.strip() for x in block.split(','))=={'propext','Classical.choice','Quot.sound'} for block in blocks)
audit();now=workspace_drift();current=not now and all(not run[k] for run in [a,b] for k in ['workspace_drift_before','workspace_drift_after']);result={'status':'MATCHED_PASS','author_path':str(A),'peer_path':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,'manifest_sha256':mh,'survey_manifest_sha256':sh,'driver_sha256':dh,'compare_sha256':ch,'rows':len(a['records']),'matched_rows':[{'name':r['name'],'object_sha256':r['object_sha256'],'log_sha256':r['log_sha256'],'warnings':r['warnings']} for r in a['records']],'guarded_file_count':len(files),'workspace_drift':{'author_before':a['workspace_drift_before'],'author_after':a['workspace_drift_after'],'peer_before':b['workspace_drift_before'],'peer_after':b['workspace_drift_after'],'comparison_final':now},'workspace_matches_snapshot_through_observations':current,'boundary':m['boundary']};(D/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print('MATCHED_PASS',len(a['records']),'rows',len(files),'files','workspace_matches',current)
