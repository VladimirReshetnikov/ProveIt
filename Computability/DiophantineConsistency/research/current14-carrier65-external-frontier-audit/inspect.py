#!/usr/bin/env python3
"""Read-only bounded recorded external routes and source-header observations."""
from pathlib import Path
from collections import Counter,deque
import hashlib,json,os,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
P=D/'research/current14-coherent-extension-refactor-retry05-runner';A=P/'attempt01'
OLD=Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PROV=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun');PKG=PROV/'package-lib'
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
LEAN=TOOL.parent.parent/'bin/lean'
MATH=Path('/home/codex/src/Proofs/.lake/packages/mathlib')
manifest_path=D/'reviews/foundation-provider-recovery/input-manifest.json'
audit_path=D/'reviews/foundation-provider-independent-audit/receipt.json'
SUFFIX=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
BASE_SUFFIX=SUFFIX[:10]
cache={}
def sha(p):
 p=Path(p); key=str(p.resolve(strict=True))
 if key not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for v in iter(lambda:f.read(1024*1024),b''):h.update(v)
  cache[key]=h.hexdigest()
 return cache[key]
def pin(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_text())
plan=pin(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
s=pin(A/'state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
base=pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
prov=pin(PROV/'build-all-receipt.json','7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6')
manifest=pin(manifest_path,'491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d')
audit=pin(audit_path,'60b8bcf556c275a33cbd133f1729fef439a2eaf4c3377d53e4ddbcafb9632a9e')
assert s['status']=='FAILED' and s['failure']=="Refusal('disk_floor')" and base['status']=='PASS'
assert len(s['rows'])==240 and len(base['records'])==1000
assert prov['status']=='BUILT' and prov['exit_code']==0 and prov['manifest_sha256']==sha(manifest_path)
assert base['provider_receipt_sha256']==sha(PROV/'build-all-receipt.json')
assert sha(Path(base['snapshot'])/'manifest.json')==base['manifest_sha256']
assert audit['status']=='PASS_PROVIDER_POINT_IN_TIME_AUDIT_OUTER_EXIT_UNOBSERVED' and not audit['outer_process_exit_observed']
assert sha(LEAN)==manifest['lean_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(PROV/'build-all.log')==prov['log_sha256']
for path,want in manifest['configs_sha256'].items():assert sha(PROV/path)==want,path

def check_guard(path,expected):
 q=Path(path)
 if expected is None: assert not os.path.lexists(q),path
 else: assert q.is_file() and str(q.resolve(strict=True))==expected['realpath'] and sha(q)==expected['sha256'],path
# Build the recorded prefix frontier, retaining only external edges.
rows={r['module']:r for r in base['records']};assert len(rows)==1000
prefix=set();prefix_ext=Counter();base_seeds=set();records={};prefix_guard={}
for row in s['rows'][:239]:
 for dep,v in row['dependencies'].items():
  if dep in rows:base_seeds.add(dep)
  elif dep not in prefix:
   assert dep in plan['external_direct'] and v['sha256']==plan['external_direct'][dep]['sha256'] and v['realpath']==plan['external_direct'][dep]['realpath']
   prefix_ext[dep]+=1
   if dep in records:assert records[dep]['sha256']==v['sha256'] and records[dep]['realpath']==v['realpath']
   else:records[dep]=v
   for root in (OLD,PKG,TOOL):
    for suf in SUFFIX:
     key=str(root/(dep.replace('.','/')+suf));assert key in row['direct_guard']
     val=row['direct_guard'][key]
     if key in prefix_guard:assert prefix_guard[key]==val
     else:prefix_guard[key]=val
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],dep
 prefix.add(row['module'])
assert len(prefix)==239 and sum(prefix_ext.values())==343 and prefix_ext['Init']==239 and len(prefix_ext)==55
for p,v in prefix_guard.items():check_guard(p,v)
# Follow only saved base project edges from prefix base seeds. This is not
# a compiled-object import traversal or full external package closure.
base_index={r['module']:i for i,r in enumerate(base['records'])}
seen=set();todo=deque(sorted(base_seeds));base_ext=Counter();base_project_edges=0;base_obj={}
while todo:
 n=todo.popleft()
 if n in seen:continue
 seen.add(n);r=rows[n];obj=BASE/'lib'/(n.replace('.','/')+'.olean')
 assert obj.is_file() and sha(obj)==r['object_sha256'],n;base_obj[n]=r['object_sha256']
 assert r['exit']==0 and sha(r['log'])==r['log_sha256'],n
 source=Path(base['snapshot'])/'src'/(n.replace('.','/')+'.lean')
 assert source.is_file() and sha(source)==r['source_sha256'],n
 for dep,v in r['direct_inputs'].items():
  q=Path(v['path']);assert q.is_file() and sha(q)==v['sha256'],(n,dep)
  if v['kind']=='project':
   assert dep in rows and base_index[dep]<base_index[n] and v['sha256']==rows[dep]['object_sha256'],(n,dep)
   assert q.resolve()==(BASE/'lib'/(dep.replace('.','/')+'.olean')).resolve()
   base_project_edges+=1;todo.append(dep)
  else:
   assert v['kind']=='package',v
   g=base['guarded_companions'][str(q)];assert g is not None and g['sha256']==v['sha256'] and str(q.resolve())==g['realpath']
   base_ext[dep]+=1
   if dep in records:assert records[dep]['sha256']==v['sha256'] and records[dep]['realpath']==g['realpath'],dep
   else:records[dep]={'path':str(q),'realpath':g['realpath'],'sha256':v['sha256']}
assert len(base_seeds)==39 and len(seen)==172 and base_project_edges==240
assert sum(base_ext.values())==208 and len(base_ext)==23
base_guard={}
for dep in base_ext:
 for suf in BASE_SUFFIX:
  k=str(PKG/(dep.replace('.','/')+suf));assert k in base['guarded_companions'];base_guard[k]=base['guarded_companions'][k]
for p,v in base_guard.items():check_guard(p,v)
allnames=set(prefix_ext)|set(base_ext)
math=sorted(n for n in allnames if n.startswith('Mathlib.'))
foundation=sorted(n for n in allnames if n.startswith('Foundation.'))
assert len(allnames)==69 and len(math)==65 and len(foundation)==3 and allnames==set(math)|set(foundation)|{'Init'}
# Rehash the retained Foundation receipt's complete pinned archive and artifact
# sets and recorded direct guards; this is not a second build or runtime trace.
fsrc=PROV/'lib/FormalizedFormalLogic-Foundation';flib=PROV/'.lake/build/lib/lean/Foundation'
archive=manifest['foundation_archive_files_sha256'];art=prov['foundation_artifacts']
assert len(archive)==manifest['foundation_archive_file_count']==477 and len(art)==1540
assert {str(q.relative_to(fsrc)) for q in fsrc.rglob('*') if q.is_file()}==set(archive)
assert {str(q.relative_to(flib)) for q in flib.rglob('*') if q.is_file()}==set(art)
for path,want in archive.items():assert sha(fsrc/path)==want,path
for path,want in art.items():assert sha(flib/path)==want,path
for path,v in prov['declared_external_guard'].items():check_guard(path,v)
assert len(prov['declared_external_guard'])==14764 and len(prov['objects'])==len(prov['foundation_source_closure'])==140
assert set(prov['objects'])==set(prov['foundation_source_closure'])
for n,want in prov['objects'].items():
 assert sha(PROV/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean'))==want,n
 source=n.replace('.','/')+'.lean';assert source in archive and sha(fsrc/source)==archive[source],n
for n in foundation:assert n in prov['objects'] and records[n]['sha256']==prov['objects'][n]
# Independently check source bytes of the 65 direct Mathlib names against
# the selected Git tree. This does not prove compiled objects came from them.
def git(*args):return subprocess.check_output(['git','-C',str(MATH),*args])
commit=git('rev-parse','HEAD').decode().strip()
assert commit==manifest['mathlib_checkout_commit']=='81a5d257c8e410db227a6665ed08f64fea08e997'
assert git('rev-parse','--show-object-format').decode().strip()=='sha1'
paths=[n.replace('.','/')+'.lean' for n in math]
raw=git('ls-tree','-r','-z','HEAD','--',*paths);blobs={}
for rec in raw.split(b'\0'):
 if not rec:continue
 meta,name=rec.split(b'\t',1);mode,kind,oid=meta.decode().split()
 assert kind=='blob';blobs[name.decode()]=oid
assert set(blobs)==set(paths)
# Strip nested Lean block comments and line comments for initial source
# headers only. This deliberately stops at the first non-header command;
# it is not a Lean parser or evidence about compiled imports.
def stripped_lines(text):
 depth=0
 for line in text.splitlines():
  out=[];i=0
  while i<len(line):
   pair=line[i:i+2]
   if depth:
    if pair=='/-':depth+=1;i+=2
    elif pair=='-/':depth-=1;i+=2
    else:i+=1
   elif pair=='/-':depth=1;i+=2
   elif pair=='--':break
   else:out.append(line[i]);i+=1
  yield ''.join(out).strip(),depth
 assert depth==0

def imports(text):
 result=[]
 for line,depth in stripped_lines(text):
  if not line or line in ('module','prelude'):continue
  m=re.fullmatch(r'((?:(?:public|private|meta)\s+)*)import\s+(.+)',line)
  if not m:break
  words=m.group(2).split();all_mode=bool(words and words[0]=='all')
  if all_mode:words=words[1:]
  assert words and all(re.fullmatch(r'[A-Za-z0-9_.]+',w) for w in words),line
  for w in words:result.append({'module':w,'all':all_mode,'modifiers':m.group(1).split()})
 return result
math_sources=[];next_names=set();import_all=[];trace_count=0
for n,rel in zip(math,paths):
 p=MATH/rel;data=p.read_bytes();git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert git_blob==blobs[rel],rel
 head=imports(data.decode());next_names.update(e['module'] for e in head)
 import_all.extend({'source':n,'module':e['module']} for e in head if e['all'])
 assert records[n]['realpath']==str((MATH/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean')).resolve())
 companions={}
 for suf in BASE_SUFFIX:
  key=str(PKG/(n.replace('.','/')+suf))
  assert key in prefix_guard or key in base_guard,(n,suf)
  vals=[g[key] for g in (prefix_guard,base_guard) if key in g]
  assert all(v==vals[0] for v in vals) and vals[0] is not None,(n,suf)
  check_guard(key,vals[0]);companions[suf]=vals[0]
 trace=PKG/(n.replace('.','/')+'.trace');assert trace.is_file();tr=json.loads(trace.read_text());assert 'depHash' in tr and 'outputs' in tr
 trace_count+=1
 math_sources.append({'module':n,'source':str(p),'source_sha256':hashlib.sha256(data).hexdigest(),'git_blob_sha1':git_blob,'olean_sha256':records[n]['sha256'],'recorded_package_companions':companions,'lake_trace_sha256':sha(trace),'initial_imports':head})
next_missing=[]
for n in sorted(next_names):
 if not any((root/(n.replace('.','/')+'.olean')).is_file() for root in (PKG,TOOL)):next_missing.append(n)
# These are per-file presence observations, not Lean namespace-first selection.
print(json.dumps({'scope':'recorded prefix/base frontier, retained Foundation evidence and Mathlib source headers; no Lean, compiled-import closure or dynamic provenance',
 'prefix_external_edges':sum(prefix_ext.values()),'prefix_external_unique':len(prefix_ext),'prefix_external_names':dict(sorted(prefix_ext.items())),
 'prefix_external_guard_distinct':len(prefix_guard),'prefix_external_guard_present':sum(v is not None for v in prefix_guard.values()),
 'base_seed_names':len(base_seeds),'reachable_recorded_base_modules':len(seen),'base_project_edges':base_project_edges,
 'reachable_base_external_edges':sum(base_ext.values()),'reachable_base_external_unique':len(base_ext),'reachable_base_external_names':dict(sorted(base_ext.items())),
 'base_external_guard_paths_checked':len(base_guard),'combined_external_unique':len(allnames),
 'foundation_names':foundation,'foundation_provider_receipt_sha256':sha(PROV/'build-all-receipt.json'),
 'foundation_source_archive_files_checked':len(archive),'foundation_artifacts_checked':len(art),'foundation_target_objects_checked':len(prov['objects']),
 'foundation_recorded_external_guard_paths_checked':len(prov['declared_external_guard']),'foundation_outer_process_exit_observed':audit['outer_process_exit_observed'],
 'mathlib_git_head':commit,'mathlib_source_rows':math_sources,'mathlib_recorded_package_companion_paths_checked':len(math)*len(BASE_SUFFIX),'mathlib_trace_files_observed':trace_count,
 'source_header_import_edges':sum(len(r['initial_imports']) for r in math_sources),
 'source_header_next_names':sorted(next_names),'source_header_next_missing_file_candidates':next_missing,
 'source_header_import_all_edges':import_all,'lean_binary_sha256':sha(LEAN),'init_object_sha256':records['Init']['sha256']},sort_keys=True,indent=2))
