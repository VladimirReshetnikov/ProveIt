#!/usr/bin/env python3
"""Point-in-time same-side indexed mass and carry closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';AUDIT=ROOT/'Computability/DiophantineConsistency/reviews/compact44-graph-temporal-carry-pair-independent-audit';PARENT=Path('/tmp/ipra-graph-temporal-carry-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
assert H(AUDIT/'CHECK.json')=='eab1a508f2b84c27883f526e882bf0852045580fa690f86948bf834b4557cb0e' and H(AUDIT/'terminal-observation.json')=='7d15ef6ba86cd61fd85f7a37c9a26c42d116258368a3a9fcec3a06ea1903eb19'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_GRAPH_TEMPORAL_CARRY_PAIRED_ARTIFACT_AUDIT' and a['receipt_sha256']=='d4221b3e0919af4718ecb92fc731aceec96ad3472ea75b2d846fb69814ac0c14' and a['overlay_objects_per_side']==178 and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
RAW=[
('CompactModelStencilSlack','compact44-model-stencil-slack-prototype/CompactModelStencilSlack.lean','ec8adf6b20','ce4d71c1f026c7db97bda895fa2db7626fc9af71d71247b45fb405c4bee2bec5'),
('CompactGenericAlignedMass','compact44-separated-band-mass-prototype/CompactGenericAlignedMass.lean','37fef5671c','7cab029d23691f666660a8c2346567114e07af7f6cfdd8396354725e95322463'),
('CompactSelectorMassBridge','compact44-separated-band-mass-prototype/CompactSelectorMassBridge.lean','37fef5671c','e6ce14f9483c931419c4f58e425058b2f07e51cfc4a31dc259bbf3ed5ef005ab'),
('CompactIndexedMass','compact44-indexed-band-mass-prototype/CompactIndexedMass.lean','a9a3100198','da343e88a58594cc23d553f4e34719da4a1f68ccf0c0c106eccfb186e8c4b9ba'),
('CompactFinIndexedMass','compact44-indexed-band-mass-prototype/CompactFinIndexedMass.lean','a9a3100198','b3d184e0bc50a35c1f5542cbc1b039bf38a02f7dd15a8160cae6ebf9fa39bf78'),
('CompactConcreteIndexedMass','compact44-indexed-band-mass-prototype/CompactConcreteIndexedMass.lean','a9a3100198','92d6515592effc645489a4da7324b8ce3b0afefe3647bac6df43944f8e45509d'),
('CompactConcreteIndexedModel','compact44-indexed-band-mass-prototype/CompactConcreteIndexedModel.lean','a9a3100198','a07fb635816c8f93766fa1755b1788a838f79fe0940800d6300e91283263a1ee'),
('CompactIndexedFlatten','compact44-indexed-band-flatten-prototype/CompactIndexedFlatten.lean','af5be62e3d','b5d3d0ec3afa84e0e183129b7a77b8992232d0f15a3aeda8b1c8a7d1e6ac5379'),
('CompactTwoBandFlatten','compact44-indexed-band-flatten-prototype/CompactTwoBandFlatten.lean','af5be62e3d','543a674d9bf08812dd5fe1965bc09d493d2bdf22dd444fbdd871677522852700'),
('CompactTwoBandCarry','compact44-indexed-band-flatten-prototype/CompactTwoBandCarry.lean','af5be62e3d','32aab0324481335c2623e6d03ca76794d942c83d83b27a6235b91eefbcabbdbb'),
('FixedGraphIndexedCarry','compact44-fixed-graph-indexed-carry-prototype/FixedGraphIndexedCarry.lean','2199db142b','855b8b1a8563b47cf23faea8a239dff0bb65a25da7d761e07177b986126d0aa7')]
rows=[];names={'DiophantineConsistency.'+x[0] for x in RAW};available=set();external=set()
for name,rel,commit,sha in RAW:
 p=BASE/rel;assert p.is_file() and H(p)==sha;blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 text=p.read_text();imports=[x[7:] for x in text.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
 for dep in imports:
  if dep not in available:assert dep not in names,('out of order',name,dep);external.add(dep)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':imports,'axiom_reports':reports});available.add('DiophantineConsistency.'+name)
assert external=={'DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.CompactCoefficientMass','DiophantineConsistency.GenericBandCarryFamily','DiophantineConsistency.FixedGraphTemporal','DiophantineConsistency.TwoBand','Mathlib.Algebra.BigOperators.Fin','Mathlib.Data.Fintype.BigOperators'}
def slots(stem):
 r={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file(),str(p);r[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:r[str(p)]=None
 return r
objects={};direct={};targets={};package={};prev=None
for side in ('author','peer'):
 lib=PARENT/side/'lib';xs={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(xs)==178
 current=[{'path':k,'sha256':H(v),'realpath':str(v.resolve())} for k,v in sorted(xs.items())];pairs=[(x['path'],x['sha256']) for x in current]
 if prev is not None:assert pairs==prev
 prev=pairs;objects[side]=current
 for dep in sorted(external):
  if dep.startswith('DiophantineConsistency.'):
   stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  z=slots(lib/Path(*row['module'].split('.')));assert all(x is None for x in z.values());targets.update(z)
for dep in sorted({'Init'}|{x for x in external if x.startswith('Mathlib.')}):
 stem=PACKAGE/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();package.update(slots(stem))
assert len(direct)==120 and len(targets)==220 and len(package)==30
print(json.dumps({'status':'PRELIMINARY_INDEXED_MASS_CARRY_SOURCE_CLOSURE_NOT_A_BUILD','parent_audit_sha256':H(AUDIT/'CHECK.json'),'parent_receipt_sha256':a['receipt_sha256'],'source_order':rows,'parent_objects':objects,'external_direct_slots':direct,'target_slots':targets,'package_slots':package,'scope':'Point-in-time source/provider inventory only; no paired build or independent proof review; retained-byte K binding, clean-column bound, full decoder, machine equivalence and internal iPRA remain open.'},indent=2,sort_keys=True))
