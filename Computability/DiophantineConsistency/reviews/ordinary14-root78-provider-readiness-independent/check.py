from pathlib import Path
import hashlib, json, re
D = Path(__file__).resolve().parents[2]
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
OLD = Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/lib')
OVERLAY = Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
TOOL = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
hashfile = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = lambda n: D/'Lean'/Path(*n.split('.')).with_suffix('.lean')
objectpath = lambda root,n: root.joinpath(*n.split('.')).with_suffix('.olean')
invpath = D/'research/ordinary14-root78-endpoint-import-inventory/inventory.json'
inv = json.loads(invpath.read_text())
assert inv['qualified_direct_count'] == len(inv['qualified_direct_sources']) == 25
presence = []
for r in inv['qualified_direct_sources']:
 p = D/r['path']; assert hashfile(p) == r['sha256']
 o = objectpath(P72,r['module'])
 presence.append({'module':r['module'],'p72_object_present':o.is_file(),'source_sha256':r['sha256']})
missing = [x['module'] for x in presence if not x['p72_object_present']]
assert missing == ['DiophantineConsistency.Compact44.C44Short15Facts','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt']
# Bounded initial-header walk, stopping at any P72 object; this does not inspect imports of those objects.
def walk(seeds):
 missing=set(); frontier=set(); external=set(); todo=list(seeds); seen=set()
 while todo:
  n=todo.pop()
  if n in seen: continue
  seen.add(n)
  if not n.startswith('DiophantineConsistency.'):
   external.add(n); continue
  if objectpath(P72,n).is_file(): frontier.add(n); continue
  p=source(n); assert p.is_file(), n
  missing.add(n)
  for line in p.read_text().splitlines():
   m=re.match(r'^import\s+([^\s]+)',line)
   if m: todo.append(m.group(1))
   elif line.strip() and not line.strip().startswith(('--','/-','-/', '*')): break
 return {'missing_sources':[{'module':n,'sha256':hashfile(source(n))} for n in sorted(missing)],'p72_object_frontier':sorted(frontier),'external_import_names':sorted(external)}
candidates = [P72, OLD, OVERLAY,
 Path('/tmp/compact12-ipra-coherent-endpoint-20261102/lib'),
 Path('/tmp/compact12-ipra-integrated-20261102/lib'),
 Path('/tmp/p72-p13-p14-captured-endpoint-20261105/lib'),
 Path('/tmp/p72-p13-p14-translated-captured-20261105/lib'),
 Path('/tmp/p72-p13-p14-translated-fresh-20261105/lib'),
 Path('/home/codex/src/Proofs/.lake/build/lib/lean'),
 D/'.lake/build/lib/lean']
candidate_presence = [{'root':str(root),'root_exists':root.is_dir(),
                       'modules_present':[n for n in missing if objectpath(root,n).is_file()]}
                      for root in candidates]
closures = {n:walk([n]) for n in missing}
union=walk(missing)
assert len(union['missing_sources'])==76
assert [len(closures[n]['missing_sources']) for n in missing]==[74,1,2]
helperimports=['DiophantineConsistency.Compact44.CompactMaskBoundFinish','DiophantineConsistency.Compact44.CompactSymbolicPorts','DiophantineConsistency.ArithmeticStandardCasts']
assert all(objectpath(P72,n).is_file() for n in helperimports)
# Record old/new model provider provenance as supplied by their separate run receipts.
mod='DiophantineConsistency.ModelDifferenceRing'
rowpath=Path('/tmp/p72-current-base-extension-attempt02-20261105/rows/0059.json')
statepath=Path('/tmp/ipra-ordinary12-coexistence-pair-01/author/child-output/state.json')
row=json.loads(rowpath.read_text()); state=json.loads(statepath.read_text())
record=next(r for r in state['records'] if r['module']==mod)
assert row['status']=='PASS' and state['status']=='PASS' and record['exit']==0
assert row['source_sha256']==record['source_sha256']==hashfile(source(mod))
assert hashfile(Path('/tmp/ipra-ordinary12-coexistence-source-03/src/DiophantineConsistency/ModelDifferenceRing.lean'))==row['source_sha256']
pobj=objectpath(P72,mod); oobj=objectpath(OLD,mod); overlay=objectpath(OVERLAY,mod)
assert hashfile(pobj)==row['object_sha256'] and hashfile(oobj)==record['object_sha256']
assert hashfile(overlay)==hashfile(oobj) != hashfile(pobj)
inputs={n:x['sha256'] for n,x in row['dependencies'].items()}
assert inputs=={n:x['sha256'] for n,x in record['direct_inputs'].items()}
assert hashfile(TOOL)==state['lean_sha256']
refs=[]
for item in inv['drafts_topological']:
 text=(D/item['path']).read_text()
 if 'C44Short15Facts' in text:
  refs.append({'path':item['path'],'imports':len(re.findall(r'^import DiophantineConsistency\.Compact44\.C44Short15Facts$',text,re.M)),'references':text.count('C44Short15Facts.port_bounds')})
assert sum(r['imports'] for r in refs)==4 and sum(r['references'] for r in refs)==6
print(json.dumps({'inventory_sha256':hashfile(invpath),'qualified_direct':presence,'targeted_root_presence':candidate_presence,'per_seed_walk':closures,'union_walk':union,'helper_imports':[{'module':n,'p72_object':str(objectpath(P72,n)),'sha256':hashfile(objectpath(P72,n))} for n in helperimports],'candidate_refactor_sites':refs,'model_difference_ring':{'source_sha256':row['source_sha256'],'p72_receipt_sha256':hashfile(rowpath),'old_receipt_sha256':hashfile(statepath),'p72_object':{'path':str(pobj),'realpath':str(pobj.resolve()),'sha256':hashfile(pobj)},'old_object':{'path':str(oobj),'realpath':str(oobj.resolve()),'sha256':hashfile(oobj)},'overlay_object':{'path':str(overlay),'realpath':str(overlay.resolve()),'sha256':hashfile(overlay)},'equal_recorded_direct_input_hashes':inputs},'compiler':{'path':str(TOOL),'sha256':hashfile(TOOL),'toolchain_file':(D.parents[1]/'lean-toolchain').read_text().strip()},'lean_run':False},indent=2,sort_keys=True))
