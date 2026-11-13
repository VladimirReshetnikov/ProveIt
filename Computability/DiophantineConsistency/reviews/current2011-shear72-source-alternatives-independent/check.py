#!/usr/bin/env python3
"""Review isolated source deltas and selected lexical graph, without Lean."""
import copy,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear72-joint-ipra-source-plan/selection.json':'ec90d8f8e746c442555badb4f3cbb91efb3a124b30879ead9fe2a8eeb7c5bf1b',
'research/current2011-shear72-reverse-magnitude-draft/Shear72ReverseMagnitude.lean.src':'70b8b4f932357d6f6a6c5b23f7b98c2bd699a0413b4e99f58e95179b71ce998b',
'research/current2011-shear72-magnitude-modelarithmetic-selection/README.md':'01bb58423a913495e4d5b4cc72dd29916e7da09ee5cec186854dda6be88a2f42',
'research/current2011-shear72-magnitude-modelarithmetic-selection/Shear72ReverseMagnitude.lean.src':'5bf58d3a69cc44b391d9ff664969eca4aea12788cc13aaf6f4417ec07e1475d9',
'research/current2011-shear72-magnitude-modelarithmetic-selection/check.py':'319d7a20812d20197c57d8c1c229fc38dc984fa047ead639556790090a92bfbd',
'research/current2011-shear72-magnitude-modelarithmetic-selection/pins.json':'0b433dfbb7ee69f30303cb077054c5f79cf26585cf95826fa182ab1c957bfcd1',
'research/current2011-shear72-magnitude-modelarithmetic-selection/selection.json':'7b41d1ec697ac0d011f7d06c1e71bf24ef0ebd9adc8b70868fb95b5725417c90',
'research/current2011-shear72-magnitude-modelarithmetic-selection/receipt.json':'b9edf2af736f2daed2787ac16721f7891aa2d43e87fdf8be721cbc9b2efa2a20',
'research/current2011-shear72-private-extraction-source-selection/README.md':'b2ad9195efcf45fe5545bcea8e5d44103c71c17d58d3e58bd127eccf3d20824a',
'research/current2011-shear72-private-extraction-source-selection/check.py':'6999d1091beb26683457c34b180e0d337c131c5f7f97304d1a049376b8c6ab63',
'research/current2011-shear72-private-extraction-source-selection/pins.json':'dcc6c520b587019ec99cd2ad7dbd5c741db130c0c01df3ba00d6869af26f1c68',
'research/current2011-shear72-private-extraction-source-selection/selection.json':'0d1dea19eeec8d8716ce4fe338452ad4c2efba35df00f3eccf1449ecef1348c2',
'research/current2011-shear72-private-extraction-source-selection/receipt.json':'ed1b62e771a10edc254c6b1f45952c0294e4506db4c7d359de6865f6fca0b006',
'Lean/DiophantineConsistency/ModelArithmetic.lean':'2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/ZRows/CoprimeSquares.lean':'263e2de4a7ab0d1006255115f280e6260158f6bff0289a5da06921e40a850801',
'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean':'5e7ef8c7983af9a713b30a02616f00f81c3654b75574fecae944fee369c862f6',
'research/current2011-ordinary94-six-module-build/attempt05-failed/modified-source.lean':'415e74a23218889f43159a8e96915be93ca54446b3dd3ad69927ac492b16a83d',
'research/current2011-ordinary94-six-module-build/attempt05/result.json':'d2848efcaa6b3aadc58dec758a33e08e5999e84ec4d1020a431a2736eac39fb3'}
def need(b,m):
 if not b:raise RuntimeError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def read(p):return (root/p).read_text()
for p,h in pins.items():need(sha((root/p).read_bytes())==h,'pin '+p)
old=read('research/current2011-shear72-reverse-magnitude-draft/Shear72ReverseMagnitude.lean.src');new=read('research/current2011-shear72-magnitude-modelarithmetic-selection/Shear72ReverseMagnitude.lean.src')
edits=[('import DiophantineConsistency.ZRows.CoprimeSquares','import DiophantineConsistency.ModelArithmetic'),('open ModelDifferenceRing ZRowsCoprimeSquares','open ModelDifferenceRing'),('obtain ⟨n,habs⟩ := abs_eq_ι z','obtain ⟨n,habs⟩ := nonneg_iff.mp (abs_nonneg z)')]
for a,b in edits:
 need(old.count(a)==1,'delta count');old=old.replace(a,b,1)
need(old==new,'unexpected source delta')
model=read('Lean/DiophantineConsistency/ModelArithmetic.lean');diff=read('Lean/DiophantineConsistency/ModelDifferenceRing.lean');cop=read('Lean/DiophantineConsistency/ZRows/CoprimeSquares.lean')
need('import DiophantineConsistency.ModelDifferenceRing' in model and 'import DiophantineConsistency.DiscreteOrderedRingFacts' in model and 'import DiophantineConsistency.ArithmeticNegativeNorms' in model,'new source imports')
need('theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in diff,'nonneg direction')
need('theorem abs_eq_ι (A : DiffRing V) : ∃ a : V, |A| = ι a := nonneg_iff.mp (abs_nonneg A)' in cop,'old theorem body')
sel0=json.loads(read('research/current2011-shear72-joint-ipra-source-plan/selection.json'));sel1=json.loads(read('research/current2011-shear72-magnitude-modelarithmetic-selection/selection.json'));sel2=json.loads(read('research/current2011-shear72-private-extraction-source-selection/selection.json'))
name='DiophantineConsistency.Shear72ReverseMagnitude';expected=copy.deepcopy(sel0);expected['drafts'][name]=sel1['drafts'][name];expected['frontier'].pop('DiophantineConsistency.ZRows.CoprimeSquares');expected['frontier']['DiophantineConsistency.ModelArithmetic']=sel1['frontier']['DiophantineConsistency.ModelArithmetic'];need(expected==sel1,'magnitude selection changed extra entries')
need(sel1['drafts'][name]['imports']==['DiophantineConsistency.ModelArithmetic'],'magnitude import selection')
expected=copy.deepcopy(sel1);ex='DiophantineConsistency.ArithmeticCarrier94Extraction';expected['frontier'][ex]=sel2['frontier'][ex];need(expected==sel2,'private selection changed extra entries')
workspace=read('Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean');private=read('research/current2011-ordinary94-six-module-build/attempt05-failed/modified-source.lean')
a='simp only [hx,ht,hA,zero_add,add_zero,mul_zero,zero_mul,mul_one,one_mul,';b='simp only [hx,ht,hA,zero_add,add_zero,mul_zero,mul_one,'
need(workspace.count(a)==1 and workspace.replace(a,b,1)==private,'private exact delta')
headers=lambda text:[x.split()[1] for x in text.splitlines() if x.startswith('import ')]
need(headers(private)==headers(workspace),'private import headers')
record=json.loads(read('research/current2011-ordinary94-six-module-build/attempt05/result.json'))
sg=[x for p,x in record['guards_before'].items() if p.endswith('/ArithmeticCarrier94Extraction.lean') and x]
need(record['status']=='PASS' and record['exit']==0 and len(sg)==1 and sg[0]['sha256']==pins['research/current2011-ordinary94-six-module-build/attempt05-failed/modified-source.lean'],'recorded private source')
# Recheck the selected direct import graph independently, without provider resolution.
selected=sel2['drafts'];front=sel2['frontier'];remaining=set(selected);order=[];used=set()
for n,v in selected.items():
 data=(root/v['path']).read_bytes();need(sha(data)==v['sha256'] and headers(data.decode())==v['imports'],'selected '+n)
 for dep in v['imports']:
  if dep not in selected:need(dep in front,'unknown '+dep);used.add(dep)
need(used==set(front),'frontier set')
for n,v in front.items():
 if v['kind']!='external-unexamined':need(sha((root/v['path']).read_bytes())==v['sha256'],'frontier source '+n)
todo=['DiophantineConsistency.Shear72JointIPRA'];reachable=set()
while todo:
 n=todo.pop()
 if n in reachable:continue
 reachable.add(n);todo.extend(dep for dep in selected[n]['imports'] if dep in selected)
need(reachable==set(selected),'unreachable selected source')
while remaining:
 ready=sorted(n for n in remaining if all(dep not in remaining for dep in selected[n]['imports'] if dep in selected))
 need(ready,'cycle');order.extend(ready);remaining.difference_update(ready)
print(json.dumps({'source_pins_verified':len(pins),'magnitude_exact_substitutions':3,'same_theorem_body_and_witness_orientation':True,'private_single_simp_list_delta':True,'historical_producer_records_private_source':True,'selection_deltas_exact':True,'selected_drafts':len(order),'direct_frontier':len(front),'scope':'source comparison and lexical graph only; imports, tactics, objects and full ancestry not authenticated by Lean'},sort_keys=True,indent=2))
