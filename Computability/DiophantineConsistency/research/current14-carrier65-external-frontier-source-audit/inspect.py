#!/usr/bin/env python3
"""Bounded external source-header and recorded-provider inspection; no Lean."""
from pathlib import Path
from collections import Counter,deque
import hashlib,json,os,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
P=D/'research/current14-coherent-extension-refactor-retry05-runner'
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
FOUND=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')
SRC={
 'Mathlib':Path('/home/codex/src/Proofs/.lake/packages/mathlib'),
 'Foundation':FOUND/'lib/FormalizedFormalLogic-Foundation',
 'Init':TOOL/'src/lean', 'Lean':TOOL/'src/lean',
 'Batteries':Path('/home/codex/src/Proofs/.lake/packages/batteries'),
 'Aesop':Path('/home/codex/src/Proofs/.lake/packages/aesop'),
 'Qq':Path('/home/codex/src/Proofs/.lake/packages/Qq'),
}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.trace',
 '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib')
cache={}
def sha(p):
 p=Path(p).resolve(strict=True)
 if p not in cache:
  with p.open('rb') as f:cache[p]=hashlib.file_digest(f,'sha256').hexdigest()
 return cache[p]
def pin(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_bytes())
plan=pin(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=pin(P/'attempt01/state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
base=pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
foundation=pin(FOUND/'build-all-receipt.json','7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6')
assert state['status']=='FAILED' and state['failure']=="Refusal('disk_floor')" and base['status']=='PASS'
assert foundation['status']=='BUILT' and len(state['rows'])==240 and len(base['records'])==1000
base_by={r['module']:r for r in base['records']};assert len(base_by)==1000
prefix=state['rows'][:239]
base_seeds={n for row in prefix for n in row['dependencies'] if n in base_by}
# Recorded project edges only; no re-resolution of hidden imports.
queue=deque(sorted(base_seeds));reachable=set()
while queue:
 n=queue.popleft()
 if n in reachable:continue
 reachable.add(n)
 for dep in base_by[n]['direct_inputs']:
  if dep in base_by and dep not in reachable:queue.append(dep)
base_external={};base_reachable_external=set()
for row in base['records']:
 for n,v in row['direct_inputs'].items():
  if n in base_by:continue
  assert v['kind']=='package',(row['module'],n)
  info=base_external.setdefault(n,{'hashes':set(),'paths':set(),'records':0})
  info['hashes'].add(v['sha256']);info['paths'].add(v['path']);info['records']+=1
  if row['module'] in reachable:base_reachable_external.add(n)
for n,v in base_external.items():assert len(v['hashes'])==1,(n,v['hashes'])
prefix_external={n for row in prefix for n in row['dependencies'] if n in plan['external_direct']}
seeds=set(plan['external_direct'])|set(base_external)
assert len(plan['external_direct'])==99 and len(base_external)==106 and len(seeds)==138
assert len(prefix_external)==55 and len(base_seeds)==39 and len(reachable)==172
# Header parsing is intentionally limited: nested block and line comments are
# removed, then only initial module/prelude and single-name import commands are
# accepted. We do not parse arbitrary Lean syntax or infer implicit imports.
import_re=re.compile(r'^(?:(public)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?([A-Za-z_][A-Za-z_0-9.]*)$')
def header(text,path):
 depth=0;mode=[];edges=[]
 for lineno,line in enumerate(text.splitlines(),1):
  out=[];i=0
  while i<len(line):
   if depth:
    if line.startswith('/-',i):depth+=1;i+=2
    elif line.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   elif line.startswith('--',i):break
   elif line.startswith('/-',i):depth=1;i+=2
   else:out.append(line[i]);i+=1
  line=''.join(out).strip()
  if not line:continue
  if line in ('module','prelude'):
   mode.append(line);continue
  m=import_re.fullmatch(line)
  if m:
   edges.append({'module':m.group(4),'public':bool(m.group(1)),'meta':bool(m.group(2)),
                 'all':bool(m.group(3)),'line':lineno});continue
  if re.match(r'^(?:(?:public|meta|private)\s+)*import\b',line):
   raise AssertionError(('unsupported import header',str(path),lineno,line))
  break
 assert depth==0,('unfinished comment before code',str(path))
 return {'markers':mode,'imports':edges}
def source(n):
 root=SRC.get(n.split('.')[0]);return None if root is None else root/(n.replace('.','/')+'.lean')
def objects(n):
 rel=n.replace('.','/')
 return [r/(rel+'.olean') for r in (PKG,TOOL/'lib/lean') if (r/(rel+'.olean')).is_file()]
def observe(p):
 if not os.path.lexists(p):return None
 assert p.is_file(),str(p)
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p),'bytes':p.stat().st_size}
# Verify the saved seed object records against current selected package paths;
# this is a byte observation, not an object-to-source provenance theorem.
seed_rows={};companion_counts=Counter();foundation_companions=Counter()
for n in sorted(seeds):
 o=objects(n);assert o,n
 expected=set()
 if n in plan['external_direct']:
  expected.add(plan['external_direct'][n]['sha256'])
  assert str(o[0].resolve(strict=True))==plan['external_direct'][n]['realpath'],n
 if n in base_external:
  expected|=base_external[n]['hashes']
  for p in base_external[n]['paths']:assert sha(p) in expected,(n,p)
 assert len(expected)==1 and sha(o[0])==next(iter(expected)),n
 sp=source(n);assert sp is not None and sp.is_file(),n
 companions={}
 for suffix in SUFFIXES:
  p=PKG/(n.replace('.','/')+suffix);v=observe(p)
  if v is not None:companions[suffix]=v;companion_counts[suffix]+=1
 if n.startswith('Foundation.'):
  assert n in foundation['objects'] and foundation['objects'][n]==sha(o[0])
  assert n in foundation['foundation_source_closure']
  rel=n[len('Foundation.'):].replace('.','/')
  for suffix,val in companions.items():
   key=rel+suffix
   if key in foundation['foundation_artifacts']:
    assert foundation['foundation_artifacts'][key]==val['sha256'],(n,suffix)
    foundation_companions[suffix]+=1
 seed_rows[n]={'source':str(sp),'source_sha256':sha(sp),'recorded_object_sha256':next(iter(expected)),
  'object_candidates':[{'path':str(z),'realpath':str(z.resolve(strict=True)),'sha256':sha(z)} for z in o],
  'companions':companions,'in_plan_external':n in plan['external_direct'],
  'in_prefix_external':n in prefix_external,'in_base_all_external':n in base_external,
  'in_base_reachable_external':n in base_reachable_external,
  'base_recorded_paths':sorted(base_external.get(n,{}).get('paths',set()))}
# One generation of actual source-header expansion beyond the complete seed set.
headers={};missing_source=[];queue=deque((n,0) for n in sorted(seeds));depth={}
while queue:
 n,d=queue.popleft()
 if n in depth and depth[n]<=d:continue
 depth[n]=d;sp=source(n)
 if sp is None or not sp.is_file():missing_source.append({'module':n,'depth':d,'candidate':None if sp is None else str(sp)});continue
 data=sp.read_bytes();entry=header(data.decode('utf-8'),sp)
 headers[n]={'depth':d,'source':str(sp),'source_sha256':hashlib.sha256(data).hexdigest(),**entry}
 if d==0:
  for e in entry['imports']:
   if e['module'] not in seeds:queue.append((e['module'],1))
all_edges=[];boundary=set()
for n,row in headers.items():
 for e in row['imports']:
  all_edges.append({'from':n,**e})
  if e['module'] not in headers:boundary.add(e['module'])
all_import_edges=[e for e in all_edges if e['all']]
all_targets={}
for n in sorted({e['module'] for e in all_import_edges}):
 r={}
 for suffix in ('.olean','.olean.private','.olean.server','.ir'):
  vals=[]
  for root in (PKG,TOOL/'lib/lean'):
   p=root/(n.replace('.','/')+suffix);v=observe(p)
   if v is not None:vals.append(v)
  r[suffix]=vals
 all_targets[n]=r
summary={'seed_names':len(seeds),'plan_external_names':len(plan['external_direct']),
 'base_all_external_names':len(base_external),'base_reachable_project_producers':len(reachable),
 'base_reachable_external_names':len(base_reachable_external),'prefix_direct_external_names':len(prefix_external),
 'seed_names_by_namespace':dict(sorted(Counter(n.split('.')[0] for n in seeds).items())),
 'source_headers_by_depth':dict(sorted(Counter(str(v['depth']) for v in headers.values()).items())),
 'missing_source_count':len(missing_source),'header_edge_count':len(all_edges),
 'public_import_edges':sum(e['public'] for e in all_edges),'meta_import_edges':sum(e['meta'] for e in all_edges),
 'import_all_edges':len(all_import_edges),'import_all_unique_targets':len(all_targets),
 'depth_boundary_names':len(boundary),'seed_companion_present_counts':dict(sorted(companion_counts.items())),
 'foundation_receipt_matched_seed_artifacts':dict(sorted(foundation_companions.items()))}
print(json.dumps({'scope':'bounded source-header and recorded-object observation; no Lean dependency resolution, source-object provenance or runtime closure',
 'summary':summary,'foundation_receipt_sha256':'7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
 'seed_rows':seed_rows,'source_headers':headers,'missing_source':missing_source,
 'boundary_names':sorted(boundary),'import_all_edges':all_import_edges,'import_all_targets':all_targets},sort_keys=True,indent=2))
