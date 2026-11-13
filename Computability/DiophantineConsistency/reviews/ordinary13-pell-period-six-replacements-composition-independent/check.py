from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-six-replacements-composition-independent');P=Path('research/ordinary13-pell-period-six-replacements-composition-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
sel=json.loads((P/'selection.json').read_text());receipt=json.loads((P/'receipt.json').read_text());assert len(sel)==16
for module,spec in sel.items():
 data=Path(spec['path']).read_bytes();assert sha256(data).hexdigest()==spec['sha256']
 assert re.findall(r'^import\s+(\S+)',data.decode(),re.M)==spec['imports']
# Independent Kahn traversal and reachability; no frontier recursion/object check.
root='DiophantineConsistency.PellPeriodSixReplacementsComposition';stack=[root];seen=set();frontier=set()
while stack:
 m=stack.pop()
 if m in seen:continue
 seen.add(m)
 for child in sel[m]['imports']:
  if child in sel:stack.append(child)
  else:frontier.add(child)
assert seen==set(sel)
remaining=set(sel);ordr=[]
while remaining:
 ready=sorted(m for m in remaining if not (set(sel[m]['imports'])&remaining))
 assert ready;remaining.difference_update(ready);ordr.extend(ready)
assert set(receipt['direct_frontier'])==frontier and len(frontier)==10
for name,entry in receipt['direct_frontier'].items():
 if name.startswith('DiophantineConsistency.'):
  path=Path('Lean/DiophantineConsistency')/(name.removeprefix('DiophantineConsistency.').replace('.','/')+'.lean')
  assert entry=={'kind':'project-source','path':str(path),'sha256':sha256(path.read_bytes()).hexdigest()}
 else:assert entry=={'kind':'external-unexamined'}
pos={name:i for i,name in enumerate(receipt['topological_order'])}
assert set(pos)==set(sel) and all(pos[d]<pos[m] for m in sel for d in sel[m]['imports'] if d in sel)
S=Path(sel[root]['path']).read_text()
F=Path(sel['DiophantineConsistency.PellPeriodFullWB']['path']).read_text()
mods={'c':('PellPeriodCReplacement','bodyC','boundC'),
      'h':('PellPeriodHReplacement','bodyH','boundH'),
      'x':('PellPeriodXYReplacements','bodyX','boundX'),
      'y':('PellPeriodXYReplacements','bodyY','boundY'),
      'r':('PellPeriodFinalReplacements','bodyR','boundR'),
      't':('PellPeriodFinalReplacements','finalBody','boundT')}
for label,(module,body,bound) in mods.items():
 src=Path(sel['DiophantineConsistency.'+module]['path']).read_text()
 assert f'theorem {label}Replacement (evalBody : BodyEvaluationBridge) : Replacement {body} {bound}' in src
 assert f'(h{label}S : Hierarchy 𝚺 1 {body})' in S
 assert f'({label}Replacement evalBody)' in S
 assert f'(h{label} : Replacement {body} {bound})' in F
assert 'period_wb_of_replacements (M := M) hcS hhS hxS hyS hrS htS' in S
assert '(cReplacement evalBody) (hReplacement evalBody)' in S
assert '(xReplacement evalBody) (yReplacement evalBody)' in S
assert '(rReplacement evalBody) (tReplacement evalBody)' in S
assert '(evalBody : BodyEvaluationBridge)' in S
assert 'period_wb_of_body_bridge (M := M) bodyEvaluationBridge hcS hhS hxS hyS hrS htS' in S
assert 'theorem bodyEvaluationBridge : BodyEvaluationBridge' in Path(sel['DiophantineConsistency.PellPeriodFinalBodyEval']['path']).read_text()
assert 'WB M periodDef.val' in S and 'WB M periodDef.val' in F
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'selected_sources_and_header_hashes_checked':len(sel),'selected_reachable_acyclic':True,
 'direct_frontier_count':len(frontier),'six_hierarchy_and_replacement_argument_order_checked':True,
 'formula_bridge_and_upstream_closure_unelaborated':True,'frontier_provider_objects_authenticated':False,
 'lean_executed':False},indent=2,sort_keys=True))
