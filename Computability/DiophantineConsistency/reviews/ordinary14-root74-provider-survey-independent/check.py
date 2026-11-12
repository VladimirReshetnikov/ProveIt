#!/usr/bin/env python3
"""Independent bounded, read-only provider survey; no Lean invocation."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-provider-survey'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105');B=Path('/tmp/current14-standard-fresh-build-20261104');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');ROOT=D.parents[1]
def H(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
pins={A/'README.md':'7ef9e970260d0660943ecd0bbf3c875ac1f7184ee339770b3aabfcd04d250ba4',A/'inspect.py':'f7d17a0b459c783d9a02540c1a8d0c66b38575fdda7e046e9b3a5777dc2a172d',A/'observation.json':'14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab'}
tail=b"\nIndependent source review: [root74 provider survey](../../reviews/ordinary14-root74-provider-survey-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='17f5dd09a7d564b3558220b9980a2d4f9118d3f35364ee30bd66d1917dcba863'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'inspect.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
receipt=json.loads(r.stdout);orig=json.loads((D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json').read_bytes());cur=json.loads((D/'research/ordinary14-root74-slim-overlay/inventory.json').read_bytes());prev=json.loads((D/'research/ordinary14-root78-slim-overlay/inventory.json').read_bytes())
a={x['module']:x for x in cur['drafts_topological']};b={x['module']:x for x in prev['drafts_topological']};assert len(a)==159 and len(b)==139 and len(a.keys()-b.keys())==21 and b.keys()-a.keys()=={'Root78Endpoint'}
for name in a.keys()&b.keys():
 x=(D/'research/ordinary14-root74-slim-overlay'/a[name]['path']).read_bytes();y=(D/'research/ordinary14-root78-slim-overlay'/b[name]['path']).read_bytes();assert x==y and H(D/'research/ordinary14-root74-slim-overlay'/a[name]['path'])==a[name]['overlay_sha256']
obj=lambda root,n:root/('/'.join(n.split('.'))+'.olean')
missing=[]
for row in orig['qualified_direct_sources']:
 assert H(D/row['path'])==row['sha256']
 if not obj(P72/'lib',row['module']).is_file():missing.append(row['module'])
assert missing==receipt['original_direct_missing_p72']
pending=list(cur['direct_qualified']);seen=set();new=set();front=set();external=set()
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  external.add(n);continue
 if obj(P72/'lib',n).is_file():front.add(n);continue
 path=D/'Lean'/('/'.join(n.split('.'))+'.lean');assert path.is_file();new.add(n)
 for line in path.read_text().splitlines():
  mt=re.fullmatch(r'import\s+([A-Za-z0-9_.]+)',line.strip())
  if mt:pending.append(mt.group(1))
  elif line.strip() and not line.strip().startswith(('--','/-','-/','*')):break
assert sorted(new)==receipt['slim_cut_new_sources'] and sorted(front)==receipt['slim_cut_frontier'] and sorted(external)==sorted(receipt['slim_cut_external'])
for name,info in receipt['slim_cut_external'].items():
 p=obj(PKG,name);assert str(p)==info['path'] and str(p.resolve(strict=True))==info['realpath'] and H(p)==info['sha256']
def slots(records):
 for path,v in records.items():
  p=Path(path)
  if v is None:assert not os.path.lexists(p),path
  else:assert str(p.resolve(strict=True))==v['realpath'] and H(p)==v['sha256'],path
 return len(records)
row27=json.loads((P72/'rows/0027.json').read_bytes());row28=json.loads((P72/'rows/0028.json').read_bytes());base=json.loads((B/'state.json').read_bytes());snap=json.loads((P72/'source-snapshot.json').read_bytes());progress=json.loads((P72/'progress.json').read_bytes())
assert progress['status']=='PASS' and base['status']=='PASS'
assert row27['status']=='PASS' and row27['module']=='DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011'
assert row28['status']=='PASS' and row28['dependencies'][row27['module']]['sha256']==row27['object_sha256']
for row in (row27,row28):
 for n,d in row['dependencies'].items():assert str(Path(d['path']).resolve(strict=True))==d['realpath'] and H(d['path'])==d['sha256']
 assert H(D/'Lean'/('/'.join(row['module'].split('.'))+'.lean'))==row['source_sha256']
 assert H(obj(P72/'lib',row['module']))==row['object_sha256']
guards=[slots(row27['direct_guard']),slots(row28['direct_guard'])]
neg='DiophantineConsistency.ArithmeticNegativeNorms';rec=next(x for x in base['records'] if x['module']==neg)
assert rec['exit']==0 and H(D/'Lean'/('/'.join(neg.split('.'))+'.lean'))==rec['source_sha256'] and H(obj(P72/'lib',neg))==rec['object_sha256']
for x in rec['direct_inputs'].values():assert H(x['path'])==x['sha256']
outputs=slots(base['outputs'][neg]);dis='DiophantineConsistency.DiscreteOrderedRingFacts'
assert dis not in snap and all(x['module']!=dis for x in base['records']) and not obj(P72/'lib',dis).exists() and not obj(B/'lib',dis).exists()
for suff,info in receipt['init'].items():
 p=PKG/('Init'+suff);q=CORE/('Init'+suff)
 assert p.is_file()==info['package_exists'] and q.is_file()==info['core_exists']
 if q.is_file():assert str(q.resolve())==info['core_realpath'] and H(q)==info['core_sha256']
 if p.is_file():assert str(p.resolve())==info['package_realpath'] and H(p)==H(q)
names=set(a)|new;roots=[P72/'lib',B/'lib',PKG,CORE,ROOT/'.lake/build/lib/lean'];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib'];hits=[]
for root in roots:
 for name in names:
  for suff in suffixes:
   path=root/(name.replace('.','/')+suff)
   if os.path.lexists(path):hits.append(str(path))
assert sorted(hits)==sorted(receipt['collision_check']['hits'])
print(json.dumps({'scope':'independent read-only selected source, recorded direct edges, guards, Init and bounded name scan; no Lean or provider-readiness proof','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'shared_snapshots_checked':len(a.keys()&b.keys()),'row27_row28_guard_counts':guards,'base_output_slots':outputs,'slim_missing_sources':sorted(new),'frontier_count':len(front),'external_count':len(external),'collision_names':len(names),'collision_hits':len(hits),'author_receipt_replayed':True},sort_keys=True,indent=2))
