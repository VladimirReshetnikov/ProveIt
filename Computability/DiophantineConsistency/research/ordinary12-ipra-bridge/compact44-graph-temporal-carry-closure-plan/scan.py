#!/usr/bin/env python3
"""Point-in-time same-side graph temporal and generic carry closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';AUDIT=ROOT/'Computability/DiophantineConsistency/reviews/compact44-graph-band-pair-independent-audit';PARENT=Path('/tmp/ipra-graph-band-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
assert H(AUDIT/'CHECK.json')=='61837a3a0d01b32f7c7a929fef3945f6fef3f1724c4b9a83c4ce721fd7a7572a' and H(AUDIT/'terminal-observation.json')=='3e863deed86b42146c3096fc3b924d557bab15e4e3000dce9a2dddf9ccb8562e'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_GRAPH_BAND_PAIRED_ARTIFACT_AUDIT' and a['receipt_sha256']=='b957b92e181a90f5dd0d1b5aa2adabb12eb7ed8eac463e47c19356e2ca5182a7' and a['overlay_objects_per_side']==171 and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
RAW=[
('BandCarryInputs','compact44-band-carry-inputs-prototype/BandCarryInputs.lean','443e573c82','99741977abae45163ecbb94dd4caa03daec0cf1db370dff0ca7ba641dbe29cf5'),
('CompactBitRotation','compact44-bit-rotation-prototype/CompactBitRotation.lean','376161cae6','898d81f0a75ac14bca36cccc8f3c3db62121e85e20e99a6aacaaadf634256c42'),
('ActualTemporalBand','compact44-actual-temporal-band-prototype/ActualTemporalBand.lean','6918b2e1cb','ef5579337f2af02063c63ad6d2aa39dcbe864fbabfcb4512596cc4e0fbe2c1b9'),
('FixedGraphTemporal','compact44-fixed-graph-temporal-prototype/FixedGraphTemporal.lean','e9f2ef84f9','872b86adfcadf783ee1887043df5a83b479594df1ac55591eac954214394ba82'),
('CompactDigitBound','compact44-scaled-carry-prototype/CompactDigitBound.lean','ef9fa9c4f5','c7830171030cb85bb5e5b1952aaddaa2539f5c41d39345caf528f372235b3c3a'),
('CompactHeterogeneousCarry','compact44-heterogeneous-carry-prototype/CompactHeterogeneousCarry.lean','a863457ff0','ce587b76912f7a0579a414a16c59c75a37b5e1b3db930ce57ff7a743c3fa7b2e'),
('GenericBandCarryFamily','compact44-generic-band-carry-family-prototype/GenericBandCarryFamily.lean','0bc129e6f7','66697812c0cafee3fa8ff6280e13dee866adaa805ebef41a897df30f34952c62')]
rows=[];names={'DiophantineConsistency.'+x[0] for x in RAW};available=set();external=set()
for name,rel,commit,sha in RAW:
 p=BASE/rel;assert p.is_file() and H(p)==sha;blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 text=p.read_text();imports=[x[7:] for x in text.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
 for dep in imports:
  if dep not in available:assert dep not in names,('out of order',name,dep);external.add(dep)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':imports,'axiom_reports':reports});available.add('DiophantineConsistency.'+name)
assert external=={'DiophantineConsistency.ArithmeticCyclicWord','DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.SymbolicGraphBand','Mathlib.Data.Fintype.BigOperators'}
def slots(stem):
 r={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file(),str(p);r[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:r[str(p)]=None
 return r
objects={};direct={};targets={};package={};prev=None
for side in ('author','peer'):
 lib=PARENT/side/'lib';xs={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(xs)==171
 current=[{'path':k,'sha256':H(v),'realpath':str(v.resolve())} for k,v in sorted(xs.items())];pairs=[(x['path'],x['sha256']) for x in current]
 if prev is not None:assert pairs==prev
 prev=pairs;objects[side]=current
 for dep in sorted(external):
  if dep.startswith('DiophantineConsistency.'):
   stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  z=slots(lib/Path(*row['module'].split('.')));assert all(x is None for x in z.values());targets.update(z)
for dep in ('Init','Mathlib.Data.Fintype.BigOperators'):
 stem=PACKAGE/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();package.update(slots(stem))
assert len(direct)==60 and len(targets)==140 and len(package)==20
print(json.dumps({'status':'PRELIMINARY_GRAPH_TEMPORAL_CARRY_SOURCE_CLOSURE_NOT_A_BUILD','parent_audit_sha256':H(AUDIT/'CHECK.json'),'parent_receipt_sha256':a['receipt_sha256'],'source_order':rows,'parent_objects':objects,'external_direct_slots':direct,'target_slots':targets,'package_slots':package,'scope':'Point-in-time source/provider inventory only; no paired build, concrete carry-family instantiation, retained-byte K binding, full graph column, machine equivalence or internal iPRA theorem.'},indent=2,sort_keys=True))
