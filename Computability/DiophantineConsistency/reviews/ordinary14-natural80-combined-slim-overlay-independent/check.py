#!/usr/bin/env python3
"""Independent bounded overlay byte and header review; never invokes Lean."""
from collections import deque
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural80-combined-slim-overlay';Q=D/'research/ordinary14-natural81-combined-slim-overlay'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(P/'check_source.py','9b42aad56c0041b75e1aa76c4dd702cf7155d3c13c9e9399d10cfe5dc48cc84d')
i=json.loads(pin(P/'inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
old=json.loads(pin(Q/'inventory.json','dea1250279ce9004e6784b6179f55f775d3751829a869d94f47216347a396ba9'))
orig=json.loads(pin(D/'research/ordinary14-natural80-endpoint-import-inventory/inventory.json','47677589f08a55c6d8a46c5801476c4ffc5ffd64299ef7d1b19017eb86b09301'))
oldrows={r['module']:r for r in old['order']}; sources={r['module']:r for r in orig['drafts_topological']};rows=i['drafts_topological'];by={r['module']:r for r in rows}
assert len(rows)==len(by)==184 and len(oldrows)==173 and set(oldrows)<set(by)==set(sources)
assert len(set(by)-set(oldrows))==11 and set(by)-set(oldrows)==set(orig['natural81_comparison']['added_modules'])
assert set(p.name for p in (P/'source').iterdir())=={n+'.lean.src' for n in by}
patches={'PartialShift82To74':('47cb83c7a8cf4053e19eb7afbb391e00528b8b0ce5fdf4a2edda9c909163170e',8),'GraphPredecessors82':('44c47be7c5725bd5bbe11ed810780938c3b885eb394ae69d5bfc9797d8ce9c5e',7)}
pattern=re.compile(r"(?<![A-Za-z0-9_'])partial(?![A-Za-z0-9_'])")
order={r['module']:n for n,r in enumerate(rows)};direct=set();differences=[]
for n,row in by.items():
 b=pin(D/row['original_path'],row['original_sha256']);assert row['original_path']==sources[n]['path'] and row['original_sha256']==sources[n]['sha256']
 path=P/row['overlay_path'];assert path==P/'source'/(n+'.lean.src') and path.is_file() and not path.is_symlink()
 actual=pin(path,row['overlay_sha256'])
 if n in oldrows:
  prev=pin(Q/oldrows[n]['overlay_path'],oldrows[n]['overlay_sha256']);assert oldrows[n]['original_sha256']==row['original_sha256']
  if n in patches:
   digest,count=patches[n];alt=pin(D/'research/ordinary14-natural-partial-keyword-patch'/(n+'.lean.src'),digest)
   out=[];k=0
   for line in prev.decode().splitlines(keepends=True):
    if line.lstrip().startswith('/--'):out.append(line);continue
    line,j=pattern.subn('partialValuation',line);k+=j;out.append(line)
   assert k==count and ''.join(out).encode()==alt==actual and row['kind']=='keyword-alternative';differences.append(n)
  else: assert prev==actual and row['kind']=='natural81-overlay-snapshot'
 else:assert actual==b and row['kind']=='natural80-endpoint-addition'
 heads=[]
 for line in actual.decode().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  heads+=m.group(1).split()
 bare=[x for x in heads if '.' not in x];qual=[x for x in heads if '.' in x]
 assert bare==row['bare_imports'] and qual==row['qualified_imports']
 for dep in bare:assert dep in order and order[dep]<order[n]
 direct.update(qual)
assert set(differences)==set(patches)
# Explicitly confirm the predecessor witness edits survive as byte-identical snapshots.
for n in ('Natural81JShift','Predecessors82'):
 assert (P/'source'/(n+'.lean.src')).read_bytes()==(D/'research/ordinary14-natural-predecessor-order-patch'/(n+'.lean.src')).read_bytes()
queue=deque(['Natural80Endpoint']);seen=set()
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n);queue.extend(by[n]['bare_imports'])
assert seen==set(by)
q={r['module']:r for r in i['qualified_direct_sources']};assert set(q)==direct and len(q)==40
oldq={r['module'] for r in old['qualified_direct_sources']};assert sorted(direct-oldq)==i['additional_direct_qualified_vs_natural81'] and len(direct-oldq)==3
for name,row in q.items():
 assert row['path']=='Lean/'+name.replace('.','/')+'.lean';pin(D/row['path'],row['sha256'])
originalq={r['module']:r for r in orig['qualified_direct_sources']}
assert set(originalq)-direct=={'DiophantineConsistency.Compact44.C44Short15Facts'}
assert all(originalq[n]==q[n] for n in q)
print(json.dumps({'scope':'independent inert source, actual header and lexical graph checks; no Lean resolution or provider closure','drafts':len(rows),'reachable':len(seen),'shared':173,'shared_unchanged':171,'keyword_alternatives':len(differences),'new_drafts':11,'direct_qualified':len(q),'added_qualified':len(direct-oldq),'predecessor_edits_preserved':True},sort_keys=True,indent=2))
