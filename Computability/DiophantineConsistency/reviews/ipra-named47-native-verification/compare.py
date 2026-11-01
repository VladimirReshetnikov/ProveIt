#!/usr/bin/env python3
"""Compare focused nine-row native 47-variable replays; transitive ancestry inherited."""
import hashlib,json,os,re,shutil,sys
from pathlib import Path
if len(sys.argv)!=4:raise SystemExit('usage: compare.py PLAN AUTHOR PEER')
PLAN,A,B=(Path(x).absolute() for x in sys.argv[1:]);assert A.resolve()!=B.resolve() and not os.path.samefile(A/'state.json',B/'state.json'),'author and peer must be independent runs'
D=Path(__file__).resolve().parent;M=PLAN/'manifest.json';DR=PLAN/'replay.py';SNAP=PLAN/'sources';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean';SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
m,mh=read(M);a,ah=read(A/'state.json');b,bh=read(B/'state.json');P=Path(m['parent']);R=Path(m['workspace_root']);SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';dh=H(DR);ch=H(__file__)
assert m['status']=='FOCUSED_NAMED47_INPUT' and len(m['order'])==9
pm=m['inherited_manifest']
assert a['status']==b['status']=='PASS' and a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256']
assert a['parent']==b['parent']==str(P) and [x['module'] for x in a['records']]==[x['module'] for x in b['records']]==m['order']
files={}
def add(path,h):
 p=str(Path(path));assert p not in files or files[p]==h,(p,files[p],h);files[p]=h
for path,h in m['gate_guard'].items():assert str(Path(path).resolve())==path;add(path,h)
for path,h in pm['origin_guard'].items():assert str(Path(path).resolve())==path;add(path,h)
for path,h in pm['parent_external_direct_paths'].items():add(path,h)
add(LEAN,m['lean_sha256']);add(PLAN/'prepare.py',m['preparer_sha256'])
for root in (A,B):add(root/'manifest.json',mh);add(root/'driver.py',dh)
for n,row in m['sources'].items():
 p=SNAP/'DiophantineConsistency'/(n+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();add(p,row['sha256'])
for rel,row in m['parent_inventory'].items():assert str((P/'lib'/rel).resolve())==row['resolved_path'];add(P/'lib'/rel,row['sha256'])
for row in pm['external'].values():
 for path,item in row['companions'].items():
  if item is not None:add(path,item['sha256'])
for path,item in pm['fallback_companions'].items():
 if item is not None:add(path,item['sha256'])
for path,item in pm['inherited_fallback_companions'].items():
 if item is not None:add(path,item['sha256'])
for group in m['model_guards']:
 for path,item in group.items():
  if item is not None:add(path,item['sha256'])
def guards(rows):
 for path,row in rows.items():
  if row is None:assert not os.path.lexists(path),path
  else:assert Path(path).is_file() and str(Path(path).resolve())==row['realpath'] and H(path)==row['sha256'],path
def norm(path,root):
 p=Path(path)
 for tag,base in (('project',root/'lib'),('package',PKG),('toolchain',TOOL)):
  if p.is_relative_to(base):return tag+':'+str(p.relative_to(base))
 raise AssertionError(('unapproved direct input',str(p)))
def project_inv(root):
 out={}
 for d,_,fs in os.walk(root/'lib',followlinks=True):
  for n in fs:
   if n.endswith(SIDECARS):
    p=Path(d)/n;out[str(p.relative_to(root/'lib'))]={'sha256':H(p),'resolved_path':str(p.resolve())}
 return out
def expected(root,state):
 out=dict(m['parent_inventory'])
 for row in state['records']:
  n=row['module'];p=root/'lib'/'DiophantineConsistency'/(n+'.olean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute()
  out['DiophantineConsistency/'+n+'.olean']={'sha256':row['object_sha256'],'resolved_path':str(p.absolute())}
 return out
expa,expb=expected(A,a),expected(B,b)
for x,y in zip(a['records'],b['records']):
 n=x['module'];assert all(x.get(k)==y.get(k) for k in ('module','exit','source_sha256','object_sha256','log_sha256')) and x['exit']==y['exit']==0
 assert x['source_sha256']==m['sources'][n]['sha256']
 normalized=[]
 for root,row in ((A,x),(B,y)):
  obj=root/'lib'/'DiophantineConsistency'/(n+'.olean');log=root/'logs'/(n+'.log');add(obj,row['object_sha256']);add(log,row['log_sha256']);text=log.read_text()
  assert 'error:' not in text and 'sorryAx' not in text and 'warning:' not in text and not re.search(r'\b(?:sorry|admit)\b',text)
  if n.endswith('Checks'):
   reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",text,re.S);wanted={'AdaptiveNamedValues47Checks':10,'IPRANamedValues47NativeChecks':3}[n]
   assert len(reports)==wanted and all({q.strip() for q in z.split(',') if q.strip()} <= {'propext','Classical.choice','Quot.sound'} for _,z in reports),(n,reports)
  inputs={};modules=set()
  for path,item in row['direct_inputs'].items():
   key=norm(path,root);assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256'];add(item['realpath'],item['sha256']);inputs[key]=item['sha256']
   rel=key.split(':',1)[1];assert rel.endswith('.olean');modules.add(rel[:-len('.olean')].replace('/','.'))
  assert modules-{'Init'}==set(m['sources'][n]['imports'])-{'Init'}
  guards(row['guards']);normalized_guards={norm(path,root):(None if info is None else info['sha256']) for path,info in row['guards'].items()}
  normalized.append((inputs,normalized_guards))
 assert normalized[0]==normalized[1],('different direct inputs or companions',n)
def external():
 assert set(pm['parent_external_direct_paths'])==set(pm['parent_external_resolved_paths'])
 assert all(str(Path(path).resolve())==v for path,v in pm['parent_external_resolved_paths'].items()) and all(not os.path.lexists(p) for p in pm['parent_external_absent_paths'])
 for name,row in pm['external'].items():
  rel=name.replace('.', '/')+'.olean';p=next((q for q in (PKG/rel,TOOL/rel) if q.is_file()),None);assert p is not None and str(p.resolve())==row['selected'];guards(row['companions'])
 guards(pm['fallback_companions']);guards(pm['inherited_fallback_companions'])
 for group in m['model_guards']:guards(group)
def audit():
 assert H(M)==mh and H(DR)==dh and H(__file__)==ch and H(A/'state.json')==ah and H(B/'state.json')==bh
 assert all(H(path)==h for path,h in files.items())
 assert all(str(Path(p).resolve())==p for p in m['gate_guard']) and all(str(Path(p).resolve())==p for p in pm['origin_guard'])
 assert all((p:=SNAP/'DiophantineConsistency'/(n+'.lean')).is_file() and not p.is_symlink() and p.resolve()==p.absolute() for n in m['sources'])
 assert all(str((P/'lib'/rel).resolve())==row['resolved_path'] for rel,row in m['parent_inventory'].items())
 external();assert project_inv(P)==m['parent_inventory'] and project_inv(A)==expa and project_inv(B)==expb
 for state in (a,b):
  for row in state['records']:guards(row['guards'])
def drift():
 out=[]
 for n,row in m['sources'].items():
  p=SRC/(n+'.lean')
  try:actual=H(p) if p.is_file() else None
  except OSError:actual=None
  if actual!=row['sha256']:out.append({'module':n,'expected':row['sha256'],'actual':actual})
 return out
audit()
for n in ('receipt.json','author-state.json','independent-state.json','author-logs','independent-logs'):assert not os.path.lexists(D/n),('refusing to overwrite',n)
for root,label,state_hash in ((A,'author',ah),(B,'independent',bh)):
 dest=D/(label+'-logs');dest.mkdir();shutil.copyfile(root/'state.json',D/(label+'-state.json'));assert H(D/(label+'-state.json'))==state_hash
 for row in a['records']:
  n=row['module']+'.log';shutil.copyfile(root/'logs'/n,dest/n);assert H(dest/n)==row['log_sha256']
audit();d1=drift();audit();d2=drift()
out={'status':'MATCHED_PASS','author_path':str(A),'peer_path':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,'manifest_sha256':mh,'driver_sha256':dh,'compare_sha256':ch,'rows':len(a['records']),'guarded_file_count':len(files),'matched_rows':[{'module':x['module'],'object_sha256':x['object_sha256'],'log_sha256':x['log_sha256']} for x in a['records']],'workspace_suffix_source_drift':d1,'workspace_suffix_source_drift_confirm':d2,'boundary':m['boundary']}
with (D/'receipt.json').open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
print('MATCHED_PASS',len(a['records']),'rows',len(files),'files',flush=True)
