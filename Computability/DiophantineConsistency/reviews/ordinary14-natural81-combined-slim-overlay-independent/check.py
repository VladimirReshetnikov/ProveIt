#!/usr/bin/env python3
"""Independent bounded overlay byte and header review; does not invoke Lean."""
from collections import deque
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
P=D/'research/ordinary14-natural81-combined-slim-overlay'
def sha(b): return hashlib.sha256(b).hexdigest()
def pin(path,h):
 b=path.read_bytes(); assert sha(b)==h,(str(path),sha(b)); return b
pin(P/'check_source.py','29b100269585104222c6bc43f7abcbacf233f8e7165214a18f327bfcc074a464')
i=json.loads(pin(P/'inventory.json','dea1250279ce9004e6784b6179f55f775d3751829a869d94f47216347a396ba9'))
base=json.loads(pin(D/'research/ordinary14-root74-slim-overlay/inventory.json','b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'))
orig=json.loads(pin(D/'research/ordinary14-natural81-endpoint-import-inventory/inventory.json','bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40'))
old={r['module']:r for r in base['drafts_topological']}; old81={r['module']:r for r in orig['drafts_topological']}
rows=i['order']; assert len(rows)==173 and len({r['module'] for r in rows})==173
by={r['module']:r for r in rows}; assert set(by)==set(old81)
assert set(old)-set(by)=={'Root74Endpoint'} and len(set(old)&set(by))==158 and len(set(by)-set(old))==15
assert set(p.name for p in (P/'source').iterdir())=={n+'.lean.src' for n in by}
fix={
 'Natural81JShift':(b'simpa [w] using hj',b'simpa [w, add_comm] using hj'),
 'Predecessors82':('  exact ⟨f, r, y, hf, hr, hy⟩'.encode(), '  exact ⟨f, r, y, by simpa [add_comm] using hf, by simpa [add_comm] using hr,\n    by simpa [add_comm] using hy⟩'.encode())}
before=b'import DiophantineConsistency.Compact44.C44Short15Facts';after=b'import CompactPortBoundsSlim'
refold=b'C44Short15Facts.port_bounds';refnew=b'CompactPortBoundsSlimDraft.port_bounds'
changes={}; qualified=set(); indexed={r['module']:k for k,r in enumerate(rows)}
for n,row in by.items():
 source=D/row['original_path']; assert source==D/old81[n]['path']; beforebytes=pin(source,old81[n]['sha256'])
 target=P/row['overlay_path']; assert target==P/'source'/(n+'.lean.src') and target.is_file() and not target.is_symlink()
 actual=pin(target,row['overlay_sha256']); assert row['original_sha256']==old81[n]['sha256']
 if n in old:
  previous=pin(D/'research/ordinary14-root74-slim-overlay'/old[n]['path'],old[n]['overlay_sha256'])
  expected=beforebytes.replace(before,after).replace(refold,refnew)
  assert actual==previous==expected
  assert row['kind']=='root74-slim-snapshot'
 elif n in fix:
  x,y=fix[n]; assert beforebytes.count(x)==1 and actual==beforebytes.replace(x,y)
  assert actual== (D/'research/ordinary14-natural-predecessor-order-patch'/(n+'.lean.src')).read_bytes()
  assert row['kind']=='predecessor-order-alternative'
 else:
  assert actual==beforebytes and row['kind']=='new-endpoint-draft'
 if actual!=beforebytes: changes[n]=(beforebytes.count(before),beforebytes.count(refold))
 # Strictly accept only the observed contiguous simple import form.
 imports=[]
 for line in actual.decode().splitlines():
  if not line.strip(): continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m: break
  imports.extend(m.group(1).split())
 bare=[x for x in imports if '.' not in x]; qual=[x for x in imports if '.' in x]
 assert bare==row['bare_imports'] and qual==row['qualified_imports']
 for dep in bare: assert dep in indexed and indexed[dep]<indexed[n],(n,dep)
 qualified.update(qual)
assert changes=={'CompactEquivalence':(1,1),'Compact78To85':(0,1),'Compact78To86':(0,1),'CompactEquivalence8687':(1,1),'CompactEquivalence8788':(1,1),'Quotient88PositiveBridge':(1,1),'Natural81JShift':(0,0),'Predecessors82':(0,0)}
q=deque(['Natural81Endpoint']);seen=set()
while q:
 n=q.popleft()
 if n in seen:continue
 seen.add(n);q.extend(by[n]['bare_imports'])
assert seen==set(by)
qrows={r['module']:r for r in i['qualified_direct_sources']}; assert set(qrows)==qualified and len(qualified)==37
for name,r in qrows.items():
 assert r['path']=='Lean/'+name.replace('.','/')+'.lean'; pin(D/r['path'],r['sha256'])
prior=set(base['direct_qualified']); assert sorted(qualified-prior)==i['additional_direct_qualified_vs_root74_slim'] and len(qualified-prior)==7
assert 'def partial {R : Type*}' in (P/'source/PartialShift82To74.lean.src').read_text()
keyword=D/'research/ordinary14-natural-partial-keyword-patch'
for n,digest,count in [('PartialShift82To74','47cb83c7a8cf4053e19eb7afbb391e00528b8b0ce5fdf4a2edda9c909163170e',8),('GraphPredecessors82','44c47be7c5725bd5bbe11ed810780938c3b885eb394ae69d5bfc9797d8ce9c5e',7)]:
 source=(P/'source'/(n+'.lean.src')).read_text(); target=pin(keyword/(n+'.lean.src'),digest).decode(); out=[]; occurrences=0
 for line in source.splitlines(keepends=True):
  if line.lstrip().startswith('/--'): out.append(line); continue
  line,k=re.subn(r"(?<![A-Za-z0-9_'])partial(?![A-Za-z0-9_'])",'partialValuation',line); occurrences+=k; out.append(line)
 assert occurrences==count and ''.join(out)==target and source!=target
assert all(n not in fix for n in ('PartialShift82To74','GraphPredecessors82'))
print(json.dumps({'scope':'independent source byte, initial-header and lexical order observations; no Lean resolution or provider closure','drafts':len(rows),'reachable':len(seen),'shared':158,'new':15,'predecessor_edits':2,'slim_edits':6,'qualified_direct':len(qualified),'new_qualified':len(qualified-prior),'unescaped_partial_declaration_present':True,'keyword_patch_changes_separate_modules':True},sort_keys=True,indent=2))
