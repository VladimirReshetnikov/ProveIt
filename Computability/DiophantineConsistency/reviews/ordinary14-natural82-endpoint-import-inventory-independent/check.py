#!/usr/bin/env python3
"""Independently compare an endpoint inventory against source headers; no Lean."""
from collections import defaultdict
from pathlib import Path
import hashlib, json
D=Path(__file__).resolve().parents[2]
def pin(rel,digest):
 data=(D/rel).read_bytes(); assert hashlib.sha256(data).hexdigest()==digest,rel
 return json.loads(data)
cur=pin('research/ordinary14-natural82-endpoint-import-inventory/inventory.json','38dab6c4960c06eac993fe207816da43adcde0e004e19f193d13d18567fe52a8')
base=pin('research/ordinary14-root74-endpoint-import-inventory/inventory.json','2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7')
n86=pin('research/ordinary14-natural86-endpoint-import-inventory/inventory.json','3ea586dd5f25b8230fa4cccee93e18bbb68ebc23beda8dfead8a9db060593732')
slim=pin('research/ordinary14-root74-slim-overlay/inventory.json','b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e')
rows=cur['drafts_topological']; qrows=cur['qualified_direct_sources']
assert len(rows)==cur['draft_count']==169 and len(qrows)==cur['qualified_direct_count']==36
byname=defaultdict(list)
for p in (D/'research').rglob('*.lean'): byname[p.stem].append(p)
seen=set(); all_qualified=set(); imports_by_module={}; paths_by_module={}
for row in rows:
 name=row['module']; path=D/row['path']; data=path.read_bytes()
 assert path.stem==name and hashlib.sha256(data).hexdigest()==row['sha256']
 assert byname[name]==[path], (name,byname[name])
 assert name not in seen
 seen.add(name); paths_by_module[name]=path
 # All observed files start with consecutive simple single-name imports.
 parsed=[]
 for line in data.decode().splitlines():
  line=line.strip()
  if not line: continue
  if not line.startswith('import '): break
  parts=line.split(); assert len(parts)==2
  parsed.append(parts[1])
 assert parsed
 bare=[x for x in parsed if '.' not in x]; qual=[x for x in parsed if '.' in x]
 assert bare==row['bare_imports'] and qual==row['qualified_imports'], name
 assert all(x in seen and x!=name for x in bare), (name,bare)
 imports_by_module[name]=bare; all_qualified.update(qual)
assert rows[-1]['path']==cur['root'] and rows[-1]['module']=='Natural82Endpoint'
# Confirm all enumerated stages are reachable from the root in the parsed graph.
todo=['Natural82Endpoint']; reachable=set()
while todo:
 n=todo.pop()
 if n not in reachable:
  reachable.add(n); todo.extend(imports_by_module[n])
assert reachable==seen
assert {r['module'] for r in qrows}==all_qualified and len(all_qualified)==36
for row in qrows:
 expected=(D/'Lean').joinpath(*row['module'].split('.')).with_suffix('.lean')
 assert expected==D/row['path'] and expected.is_file()
 assert hashlib.sha256(expected.read_bytes()).hexdigest()==row['sha256']
new={r['module']:r for r in rows}; old={r['module']:r for r in base['drafts_topological']}
old86={r['module']:r for r in n86['drafts_topological']}; ov={r['module']:r for r in slim['drafts_topological']}
common=set(new)&set(old); common86=set(new)&set(old86)
assert len(common)==158 and len(common86)==162 and set(old)==set(ov)
assert not [n for n in common if new[n]['sha256']!=old[n]['sha256']]
assert not [n for n in common if new[n]['sha256']!=ov[n]['source_sha256']]
# Independent extra check: the comparison receipt itself does not report this drift.
drift86=sorted(n for n in common86 if new[n]['sha256']!=old86[n]['sha256'])
assert not drift86
rb=cur['root74_comparison']; r86=cur['natural86_comparison']; ro=cur['slim_overlay_comparison']
qbase={r['module'] for r in base['qualified_direct_sources']}; q86={r['module'] for r in n86['qualified_direct_sources']}; qslim=set(slim['direct_qualified'])
assert rb['shared']==len(common) and rb['added_modules']==sorted(set(new)-set(old)) and rb['omitted_modules']==sorted(set(old)-set(new))
assert rb['common_source_hash_changed']==[] and rb['added_direct_qualified']==sorted(all_qualified-qbase) and rb['omitted_direct_qualified']==sorted(qbase-all_qualified)
assert r86['shared']==len(common86) and r86['added_modules']==sorted(set(new)-set(old86)) and r86['omitted_modules']==sorted(set(old86)-set(new))
assert r86['added_direct_qualified']==sorted(all_qualified-q86) and r86['omitted_direct_qualified']==sorted(q86-all_qualified)
assert ro['overlay_draft_count']==len(ov) and ro['shared_draft_modules']==len(set(new)&set(ov))
assert ro['endpoint_drafts_not_in_overlay']==sorted(set(new)-set(ov)) and ro['overlay_drafts_not_used_by_endpoint']==sorted(set(ov)-set(new))
assert ro['common_original_source_hash_changed']==[]
assert ro['endpoint_direct_qualified_not_in_overlay']==sorted(all_qualified-qslim) and ro['overlay_direct_qualified_not_in_endpoint']==sorted(qslim-all_qualified)
print(json.dumps({'scope':'bounded independent source header, hash, research-tree candidate and set comparisons; no Lean resolution or provider closure',
 'bare_modules':len(rows),'direct_qualified_sources':len(qrows),'all_reachable':len(reachable),
 'root74_shared':len(common),'natural86_shared':len(common86),'natural86_common_source_hash_drift':drift86,
 'root74_overlay_shared':len(set(new)&set(ov))},sort_keys=True,indent=2))
