#!/usr/bin/env python3
"""Independent recorded-edge traversal and retained-data audit; never invokes Lean."""
import hashlib,json,os,re,subprocess,sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
AUDIT=D/'research/current14-carrier65-external-frontier-audit'
RUN=D/'research/current14-coherent-extension-refactor-retry05-runner'
OLD=Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PROV=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun')
PKG=PROV/'package-lib'
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
MATH=Path('/home/codex/src/Proofs/.lake/packages/mathlib')

def hashpath(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def pinned(p,d):
 assert hashpath(p)==d,str(p)
 return json.loads(Path(p).read_text())
assert hashpath(AUDIT/'inspect.py')=='60b61002fa4fc04a4be766e9f6adcf3118c80320deb0d7c6000786d35d7bc168'
o=pinned(AUDIT/'observation.json','a82646153dfe8be0b6e703f0c66a4e30cf87b974a944efda680a1fe56803ee0a')
s=pinned(RUN/'attempt01/state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
plan=pinned(RUN/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
base=pinned(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
p=pinned(PROV/'build-all-receipt.json','7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6')
m=pinned(D/'reviews/foundation-provider-recovery/input-manifest.json','491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d')
a=pinned(D/'reviews/foundation-provider-independent-audit/receipt.json','60b8bcf556c275a33cbd133f1729fef439a2eaf4c3377d53e4ddbcafb9632a9e')
assert s['status']=='FAILED' and s['failure']=="Refusal('disk_floor')" and len(s['rows'])==240 and base['status']=='PASS'
assert p['status']=='BUILT' and p['exit_code']==0 and p['manifest_sha256']==hashpath(D/'reviews/foundation-provider-recovery/input-manifest.json')
assert base['provider_receipt_sha256']==hashpath(PROV/'build-all-receipt.json')
assert not a['outer_process_exit_observed']
assert hashpath(PROV/'build-all.log')==p['log_sha256']
for path,h in m['configs_sha256'].items():assert hashpath(PROV/path)==h
lean=TOOL.parent.parent/'bin/lean'
assert hashpath(lean)==m['lean_sha256']==o['lean_binary_sha256']

def guard(path,val):
 path=Path(path)
 if val is None:assert not os.path.lexists(path),str(path)
 else:assert path.is_file() and str(path.resolve(strict=True))==val['realpath'] and hashpath(path)==val['sha256'],str(path)
records={x['module']:x for x in base['records']};order={x['module']:i for i,x in enumerate(base['records'])}
assert len(records)==1000
prior=set();seeds=set();pc=Counter();pg={};ext={}
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib')
for row in s['rows'][:239]:
 for name,v in row['dependencies'].items():
  target=Path(v['path']);assert target.is_file() and str(target.resolve())==v['realpath'] and hashpath(target)==v['sha256']
  if name in records:seeds.add(name);continue
  if name in prior:continue
  pc[name]+=1;expected=plan['external_direct'][name]
  assert v['realpath']==expected['realpath'] and v['sha256']==expected['sha256']
  assert name not in ext or ext[name]==(v['realpath'],v['sha256'])
  ext[name]=(v['realpath'],v['sha256'])
  for root in (OLD,PKG,TOOL):
   for suf in suffixes:
    key=str(root/(name.replace('.','/')+suf));g=row['direct_guard'][key]
    assert key not in pg or pg[key]==g
    pg[key]=g
 prior.add(row['module'])
assert len(prior)==239 and len(seeds)==39 and sum(pc.values())==343 and len(pc)==55
assert dict(sorted(pc.items()))==o['prefix_external_names']
for path,val in pg.items():guard(path,val)
assert len(pg)==o['prefix_external_guard_distinct']
stack=list(seeds);seen=set();bc=Counter();project_edges=0
while stack:
 name=stack.pop()
 if name in seen:continue
 seen.add(name);r=records[name]
 obj=BASE/'lib'/(name.replace('.','/')+'.olean')
 assert hashpath(obj)==r['object_sha256'] and r['exit']==0 and hashpath(r['log'])==r['log_sha256']
 source=Path(base['snapshot'])/'src'/(name.replace('.','/')+'.lean')
 assert hashpath(source)==r['source_sha256']
 for dep,v in r['direct_inputs'].items():
  target=Path(v['path']);assert hashpath(target)==v['sha256']
  if v['kind']=='project':
   assert dep in records and order[dep]<order[name] and records[dep]['object_sha256']==v['sha256']
   assert target.resolve()==(BASE/'lib'/(dep.replace('.','/')+'.olean')).resolve()
   project_edges+=1;stack.append(dep)
  else:
   assert v['kind']=='package';bc[dep]+=1;g=base['guarded_companions'][str(target)]
   assert g is not None and g['sha256']==v['sha256'] and str(target.resolve())==g['realpath']
   assert dep not in ext or ext[dep]==(g['realpath'],v['sha256'])
   ext[dep]=(g['realpath'],v['sha256'])
assert len(seen)==172 and project_edges==240 and sum(bc.values())==208 and len(bc)==23
assert dict(sorted(bc.items()))==o['reachable_base_external_names']
bg={}
for name in bc:
 for suf in suffixes[:10]:
  path=str(PKG/(name.replace('.','/')+suf));bg[path]=base['guarded_companions'][path]
for path,val in bg.items():guard(path,val)
assert len(bg)==o['base_external_guard_paths_checked']==230
names=set(pc)|set(bc);math=sorted(n for n in names if n.startswith('Mathlib.'));foundation=sorted(n for n in names if n.startswith('Foundation.'))
assert len(names)==69 and len(math)==65 and len(foundation)==3 and names==set(math)|set(foundation)|{'Init'}
assert foundation==o['foundation_names'] and ext['Init'][1]==o['init_object_sha256']
# Independently rehash each retained Foundation input, output and guarded path.
fsrc=PROV/'lib/FormalizedFormalLogic-Foundation';flib=PROV/'.lake/build/lib/lean/Foundation'
archive=m['foundation_archive_files_sha256'];arts=p['foundation_artifacts']
assert set(archive)=={str(x.relative_to(fsrc)) for x in fsrc.rglob('*') if x.is_file()}
assert set(arts)=={str(x.relative_to(flib)) for x in flib.rglob('*') if x.is_file()}
for name,h in archive.items():assert hashpath(fsrc/name)==h
for name,h in arts.items():assert hashpath(flib/name)==h
assert len(archive)==477 and len(arts)==1540 and len(p['objects'])==140
assert set(p['objects'])==set(p['foundation_source_closure'])
for name,h in p['objects'].items():
 assert hashpath(PROV/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean'))==h
 assert name.replace('.','/')+'.lean' in archive
for name in foundation:assert ext[name][1]==p['objects'][name]
for path,val in p['declared_external_guard'].items():guard(path,val)
assert len(p['declared_external_guard'])==14764
# Compare actual source bytes to Git's stored blobs; do not infer object provenance.
commit='81a5d257c8e410db227a6665ed08f64fea08e997'
assert subprocess.check_output(['git','-C',str(MATH),'rev-parse','HEAD']).decode().strip()==commit==m['mathlib_checkout_commit']
# Independent line-preserving comment stripper for the simple initial headers.
def decomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
  elif depth and s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
  elif not depth and s.startswith('--',i):
   j=s.find('\n',i)
   if j<0:out.extend(' '*(len(s)-i));break
   out.extend(' '*(j-i));i=j
  else:
   out.append('\n' if s[i]=='\n' else (' ' if depth else s[i]));i+=1
 assert depth==0
 return ''.join(out)
def parse_headers(s):
 result=[]
 for line in decomment(s).splitlines():
  line=line.strip()
  if not line or line in ('module','prelude'):continue
  match=re.fullmatch(r'((?:(?:public|private|meta)\s+)*)import\s+(.+)',line)
  if not match:break
  mods=match.group(1).split();parts=match.group(2).split();is_all=parts[0]=='all'
  if is_all:parts=parts[1:]
  assert parts and all(re.fullmatch(r'[A-Za-z0-9_.]+',part) for part in parts)
  result.extend({'module':part,'all':is_all,'modifiers':mods} for part in parts)
 return result
entries={r['module']:r for r in o['mathlib_source_rows']}
assert set(entries)==set(math)
next_names=set();edge_count=0;all_edges=[];slots=0
for name in math:
 r=entries[name];rel=name.replace('.','/')+'.lean';file=MATH/rel;data=file.read_bytes()
 gitbytes=subprocess.check_output(['git','-C',str(MATH),'show',commit+':'+rel])
 assert data==gitbytes and str(file)==r['source'] and hashlib.sha256(data).hexdigest()==r['source_sha256']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob_sha1']
 assert ext[name][1]==r['olean_sha256']
 imports=parse_headers(data.decode());assert imports==r['initial_imports'];edge_count+=len(imports)
 next_names.update(x['module'] for x in imports)
 all_edges.extend({'source':name,'module':x['module']} for x in imports if x['all'])
 for suf,val in r['recorded_package_companions'].items():
  assert suf in suffixes[:10];guard(PKG/(name.replace('.','/')+suf),val);slots+=1
 trace=PKG/(name.replace('.','/')+'.trace');assert hashpath(trace)==r['lake_trace_sha256']
 tr=json.loads(trace.read_text());assert 'depHash' in tr and 'outputs' in tr
assert slots==650 and edge_count==634 and len(next_names)==546 and all_edges==o['source_header_import_all_edges'] and len(all_edges)==2
assert sorted(next_names)==o['source_header_next_names']
missing=[name for name in sorted(next_names) if not any((r/(name.replace('.','/')+'.olean')).is_file() for r in (PKG,TOOL))]
assert missing==o['source_header_next_missing_file_candidates']==[]
print(json.dumps({'scope':'independent bounded recorded-edge, retained-file and source-header review; no Lean resolution, source-to-object or runtime provenance', 'prefix_external_edges':sum(pc.values()),'reachable_base':len(seen),'base_project_edges':project_edges,'base_external_edges':sum(bc.values()),'combined_external_names':len(names),'prefix_guard_slots':len(pg),'base_guard_slots':len(bg),'foundation_archive_files':len(archive),'foundation_artifacts':len(arts),'foundation_guard_slots':len(p['declared_external_guard']),'mathlib_sources':len(math),'mathlib_companion_slots':slots,'mathlib_header_edges':edge_count,'mathlib_header_names':len(next_names),'import_all_edges':len(all_edges),'outer_foundation_exit_observed':a['outer_process_exit_observed']},sort_keys=True,indent=2))
