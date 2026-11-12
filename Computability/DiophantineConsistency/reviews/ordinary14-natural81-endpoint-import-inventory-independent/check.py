#!/usr/bin/env python3
"""Bounded independent source-header audit; does not invoke Lean."""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
P=D/'research/ordinary14-natural81-endpoint-import-inventory'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_text())
assert sha(P/'check_source.py')=='aee40da185ee13fa4def94e494eeb75e688b190e74c674d36b835afc61e24a3a'
x=read(P/'inventory.json','bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40')
b=read(D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json','2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7')
s=read(D/'research/ordinary14-root74-slim-overlay/inventory.json','b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e')
n82=read(D/'research/ordinary14-natural82-endpoint-import-inventory/inventory.json','38dab6c4960c06eac993fe207816da43adcde0e004e19f193d13d18567fe52a8')
rows=x['drafts_topological']; qrows=x['qualified_direct_sources']
assert len(rows)==x['draft_count']==173 and len(qrows)==x['qualified_direct_count']==38
byname={r['module']:r for r in rows};assert len(byname)==len(rows)
qby={r['module']:r for r in qrows};assert len(qby)==len(qrows)
# Rebuild a per-module candidate index limited to research, matching the
# documented scope. It cannot rule out other source or object roots.
candidates=defaultdict(list)
for p in (D/'research').rglob('*.lean'):candidates[p.stem].append(p)
idx={r['module']:i for i,r in enumerate(rows)}
edgecount=0;actual_qualified=set();headers={}
for r in rows:
 module=r['module'];p=D/r['path']
 assert p.is_file() and p.stem==module and sha(p)==r['sha256']
 assert len(candidates[module])==1 and candidates[module][0]==p,module
 # The observed sources use simple initial imports. Split words independently
 # and reject forms outside this limited syntax rather than guessing Lean syntax.
 imported=[]
 for line in p.read_text().splitlines():
  t=line.strip()
  if not t:continue
  pieces=t.split()
  if not pieces or pieces[0]!='import':break
  assert len(pieces)>1 and all(re.fullmatch(r'[A-Za-z0-9_.]+',v) for v in pieces[1:]),module
  imported.extend(pieces[1:])
 bare=[v for v in imported if '.' not in v]; qual=[v for v in imported if '.' in v]
 assert bare==r['bare_imports'] and qual==r['qualified_imports'],module
 for dep in bare:assert dep in idx and idx[dep]<idx[module],(module,dep)
 edgecount+=len(bare)+len(qual);actual_qualified.update(qual);headers[module]=bare
assert actual_qualified==set(qby)
for name,r in qby.items():
 p=D/r['path'];expected=(D/'Lean').joinpath(*name.split('.')).with_suffix('.lean')
 assert p==expected and p.is_file() and sha(p)==r['sha256'],name
root=Path(x['root']).stem;assert root=='Natural81Endpoint' and rows[-1]['module']==root
seen=set();todo=[root]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(headers[n])
assert seen==set(byname)
# Compare module sets and, independently of the original natural82 set-only
# comparison, current recorded source hashes for every common module.
old82={r['module']:r for r in n82['drafts_topological']}; q82={r['module'] for r in n82['qualified_direct_sources']}
extra=set(byname)-set(old82);assert set(old82)<=set(byname)
assert extra=={'P81NaturalForcedJ','Natural81JShift','StrictK0Symbolic','Natural81Endpoint'}
assert all(byname[n]['sha256']==r['sha256'] for n,r in old82.items())
assert set(qby)-q82=={'DiophantineConsistency.Compact44.CompactKernelSplit','DiophantineConsistency.Compact44.CompactSymbolicModelIff'} and q82<=set(qby)
cmp82=x['natural82_comparison'];assert cmp82['shared']==169 and set(cmp82['added_modules'])==extra
assert set(cmp82['omitted_modules'])==set(old82)-set(byname)
assert set(cmp82['added_direct_qualified'])==set(qby)-q82 and set(cmp82['omitted_direct_qualified'])==q82-set(qby)
base={r['module']:r for r in b['drafts_topological']}; overlay={r['module']:r for r in s['drafts_topological']}
assert set(base)==set(overlay) and len(base)==159
common=set(byname)&set(base);assert len(common)==158 and set(base)-set(byname)=={'Root74Endpoint'}
assert all(byname[n]['sha256']==base[n]['sha256']==overlay[n]['source_sha256'] for n in common)
assert len(set(byname)-set(overlay))==15 and x['slim_overlay_comparison']['shared_draft_modules']==158
assert set(x['slim_overlay_comparison']['endpoint_drafts_not_in_overlay'])==set(byname)-set(overlay)
assert x['root74_comparison']['common_source_hash_changed']==[] and x['slim_overlay_comparison']['common_original_source_hash_changed']==[]
qbase={r['module'] for r in b['qualified_direct_sources']};qslim=set(s['direct_qualified'])
cmpbase=x['root74_comparison'];cmpslim=x['slim_overlay_comparison']
assert cmpbase['shared']==158 and set(cmpbase['added_modules'])==set(byname)-set(base)
assert set(cmpbase['omitted_modules'])==set(base)-set(byname)
assert set(cmpbase['added_direct_qualified'])==set(qby)-qbase and set(cmpbase['omitted_direct_qualified'])==qbase-set(qby)
assert cmpslim['overlay_draft_count']==len(overlay) and set(cmpslim['overlay_drafts_not_used_by_endpoint'])==set(overlay)-set(byname)
assert set(cmpslim['endpoint_direct_qualified_not_in_overlay'])==set(qby)-qslim and set(cmpslim['overlay_direct_qualified_not_in_endpoint'])==qslim-set(qby)
endpoint=(D/x['root']).read_text()
for n in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert f'#print axioms DiophantineConsistency.Natural81EndpointDraft.{n}' in endpoint,n
print(json.dumps({'scope':'initial source-header and hash inventory only; no Lean/provider resolution','bare_drafts':len(rows),'qualified_direct_sources':len(qrows),'header_import_edges':edgecount,'endpoint_reachable_drafts':len(seen),'research_tree_candidate_uniqueness':True,'natural82_common_source_hashes_equal':len(old82),'natural82_added_modules':sorted(extra),'root74_overlay_shared':len(common),'endpoint_drafts_missing_from_overlay':len(set(byname)-set(overlay)),'axiom_commands_present_unexecuted':5},sort_keys=True,indent=2))
