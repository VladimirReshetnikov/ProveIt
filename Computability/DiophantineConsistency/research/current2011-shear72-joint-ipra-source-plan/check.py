from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-joint-ipra-source-plan')
selection=json.loads((D/'selection.json').read_text());drafts=selection['drafts'];frontier=selection['frontier'];orig=selection['original_forward']
assert sha256(Path(orig['path']).read_bytes()).hexdigest()==orig['sha256']
for n,info in drafts.items():
 data=Path(info['path']).read_bytes();assert sha256(data).hexdigest()==info['sha256'],n
 assert re.findall(r'^import\s+(\S+)',data.decode(),re.M)==info['imports'],n
for n,info in frontier.items():
 if info['kind']!='external-unexamined':
  assert sha256(Path(info['path']).read_bytes()).hexdigest()==info['sha256'],n
original=Path(orig['path']).read_text();alternate=Path(drafts['ForwardCoordinateMap']['path']).read_text()
assert original.count('import Shear72Literal\n')==1
assert alternate==original.replace('import Shear72Literal\n','import DiophantineConsistency.Shear72Literal\n',1)
assert 'Shear72Literal' not in drafts and 'DiophantineConsistency.Shear72Literal' in drafts
root='DiophantineConsistency.Shear72JointIPRA';active=set();seen=set();order=[];usedfront=set()
def visit(n):
 if n in seen:return
 assert n not in active,n
 active.add(n)
 for dep in drafts[n]['imports']:
  if dep in drafts:visit(dep)
  else:assert dep in frontier,dep;usedfront.add(dep)
 active.remove(n);seen.add(n);order.append(n)
visit(root)
assert seen==set(drafts),sorted(set(drafts)-seen)
assert usedfront==set(frontier)
s=Path(drafts[root]['path']).read_text()
for t in ['theorem parent_to_child : ParentToChild','ShearForwardCoordinateMapDraft.forward_zero v hz','theorem child_to_parent : ChildToParent','ShearReverseCoordinateMapDraft.reverse_zero v hz','Shear72ConditionalIPRADraft.same_no_zero parent_to_child child_to_parent','Shear72ConditionalIPRADraft.bridge72 parent_to_child child_to_parent','standard_translated_equivalence72 parent_to_child child_to_parent']:
 assert t in s,t
fw=Path(drafts['ForwardCoordinateMap']['path']).read_text();rv=Path(drafts['DiophantineConsistency.ShearReverseCoordinateMap']['path']).read_text();endpoint=Path(drafts['DiophantineConsistency.Shear72ConditionalIPRA']['path']).read_text()
for t in ['theorem forward_zero (v : Fin 14 → V)','∃ w : Fin 14 → V','OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports','Shear72LiteralDraft.expressionAt CurrentWindowCarry2011.ports']:assert t in fw,t
for t in ['theorem reverse_zero (v : Fin 14 → V)','∃ w : Fin 14 → V','OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports','Shear72LiteralDraft.expressionAt CurrentWindowCarry2011.ports']:assert t in rv,t
for t in ['def ParentToChild : Prop','def ChildToParent : Prop','theorem standard_translated_equivalence72']:assert t in endpoint,t
print(json.dumps({'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(),'selected_draft_count':len(drafts),'draft_topological_order':order,'direct_frontier':dict(sorted(frontier.items())),'original_alternate_exact_one_import_delta':True,'source_interface_shapes_checked':True,'lean_executed':False,'object_provider_authenticated':False},sort_keys=True,indent=2))
