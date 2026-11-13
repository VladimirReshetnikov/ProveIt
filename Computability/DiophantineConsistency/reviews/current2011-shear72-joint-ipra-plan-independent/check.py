#!/usr/bin/env python3
"""Independent lexical selected-DAG and one-line source alternative audit."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={'research/current2011-shear72-joint-ipra-source-plan/README.md':'9792f8fbc40d8207bd0ea42077f9050f4e0f694f5ea19b07e8072793a0c354d6',
'research/current2011-shear72-joint-ipra-source-plan/selection.json':'ec90d8f8e746c442555badb4f3cbb91efb3a124b30879ead9fe2a8eeb7c5bf1b',
'research/current2011-shear72-joint-ipra-source-plan/check.py':'c5f324a2a9979b02a2a87dd088dcb961143e329aabe40c81ff8dc5d9bcf92a67',
'research/current2011-shear72-joint-ipra-source-plan/receipt.json':'5b36c32fd3d27258cdb786ec82e75ac675986c91e8d23fb2c93fcd157f2d5246'}
def need(b,m):
 if not b:raise RuntimeError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
for p,h in pins.items():need(sha((root/p).read_bytes())==h,'pin '+p)
d=json.loads((root/'research/current2011-shear72-joint-ipra-source-plan/selection.json').read_bytes());draft=d['drafts'];front=d['frontier']
need(len(draft)==15 and len(front)==11 and len({x['path'] for x in draft.values()})==15,'selection counts and distinct paths')
headers={};paths=set()
for name,v in draft.items():
 data=(root/v['path']).read_bytes();need(sha(data)==v['sha256'],'draft sha '+name)
 actual=[line.split()[1] for line in data.decode().splitlines() if line.startswith('import ')]
 need(actual==v['imports'],'header '+name);headers[name]=actual;paths.add(v['path'])
for name,v in front.items():
 if v['kind']=='external-unexamined':need(name=='Mathlib','external');continue
 need(sha((root/v['path']).read_bytes())==v['sha256'],'frontier sha '+name)
original=(root/d['original_forward']['path']).read_bytes();alternative=(root/draft['ForwardCoordinateMap']['path']).read_bytes()
old=b'import Shear72Literal\n';new=b'import DiophantineConsistency.Shear72Literal\n'
need(sha(original)==d['original_forward']['sha256'] and original.count(old)==1 and alternative==original.replace(old,new,1),'one-line reconciliation')
# Build reachable closure and independent Kahn topological traversal.
rootmod='DiophantineConsistency.Shear72JointIPRA';reachable={rootmod};todo=[rootmod];usedfront=set()
while todo:
 n=todo.pop()
 for dep in headers[n]:
  if dep in draft:
   if dep not in reachable:reachable.add(dep);todo.append(dep)
  else:need(dep in front,'missing frontier '+dep);usedfront.add(dep)
need(reachable==set(draft) and usedfront==set(front),'exact closure')
remaining=set(draft);order=[]
while remaining:
 ready=sorted(n for n in remaining if all(x not in remaining for x in headers[n] if x in draft))
 need(ready,'cycle');order.extend(ready);remaining.difference_update(ready)
source=(root/draft[rootmod]['path']).read_text()
for text in ['theorem parent_to_child : ParentToChild','ShearForwardCoordinateMapDraft.forward_zero v hz','theorem child_to_parent : ChildToParent','ShearReverseCoordinateMapDraft.reverse_zero v hz','same_no_zero parent_to_child child_to_parent','bridge72 parent_to_child child_to_parent','standard_translated_equivalence72 parent_to_child child_to_parent']:
 need(text in source,'interface '+text)
print(json.dumps({'selected_drafts':len(draft),'direct_frontier_names':len(front),'all_draft_sources_and_headers_pinned':True,'all_selected_nodes_reachable':True,'independent_kahn_order':order,'exact_one_import_delta':True,'map_endpoint_source_shapes_checked':True,'scope':'lexical selected closure only; no Lean resolution, object authentication or full dependency ancestry'},sort_keys=True,indent=2))
