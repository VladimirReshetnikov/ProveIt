#!/usr/bin/env python3
"""Point-in-time same-side fractional rotation-window closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';AUDIT=ROOT/'Computability/DiophantineConsistency/reviews/compact44-indexed-graph-carry-pair-independent-audit';PARENT=Path('/tmp/ipra-indexed-graph-carry-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
assert H(AUDIT/'CHECK.json')=='fc611469130bf441fb3389e7f17edd7b9dd8bae37e7b63cee88e293bc282ce27' and H(AUDIT/'terminal-observation.json')=='b01af316500caf41eae1c918bf5db35dc9e82ac88c5581e9662aa8acc2d6ade2'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_INDEXED_GRAPH_CARRY_PAIRED_ARTIFACT_AUDIT' and a['receipt_sha256']=='ac61d16759d0af5a28304226dd397e151af4a1d5f1e49ba3dcc204c0945ba13f' and a['overlay_objects_per_side']==189 and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
RAW=[
('FractionalDigits','compact44-fractional-digits-prototype/FractionalDigits.lean','5152fadc5e','48b2ff023a27064ec4f40745f11d3140c610926529fc149524eb6819db973049'),
('AdjacentDigits','compact44-fractional-digits-prototype/AdjacentDigits.lean','5152fadc5e','6eb18b11e5c7cd6dcc919dbaf0f6cab4d89bb0881d8f08add62b6610f7b55dbb'),
('RotationWindow','compact44-rotation-adjacent-prototype/RotationWindow.lean','ce88d22a4f','789dddd37cc137051bcfa5f207554b1d06ad5f825c5ddef79323abf7fe91f272'),
('RotationAdjacent','compact44-rotation-adjacent-prototype/RotationAdjacent.lean','ce88d22a4f','efb159a4e78a2bfd7d21c59657f051c3d09d8b7159687db493204135b1f4ff6d'),
('RotationWrapped','compact44-wrapped-rotation-prototype/RotationWrapped.lean','40b71334eb','e7d43e97a59c4e47499473212fcbc12fdd476abfd009a22b798cf95710225746'),
('WrappedAdjacent','compact44-wrapped-rotation-prototype/WrappedAdjacent.lean','40b71334eb','b803e1dc9eed94cdc25d4e8fb6cbb80f58ee41dd41ccfc1320546e7bfde785ce'),
('RotationStraddling','compact44-straddling-rotation-prototype/RotationStraddling.lean','5105b2126b','9d1448cc78d3aac7a49e2b3a1e13ea7ab04697b94f6662f096622f583cc1abab'),
('StraddlingAdjacent','compact44-straddling-rotation-prototype/StraddlingAdjacent.lean','5105b2126b','701c63d6588210d116c3872a35c52d6174e9d48b7ba0406b373b66b4cefa6ded'),
('RotationCoverage','compact44-rotation-coverage-prototype/RotationCoverage.lean','a09b6d055b','846de72f6252a7b878c07ea5383de1dfea10440ea463b33e65b9179bdab52a0f'),
('RotationCoverage67','compact44-rotation-coverage-prototype/RotationCoverage67.lean','a09b6d055b','dcb28996eb38f586da6d43d8d5ed5bbe3c5d8768bfd6f563916ec86d8d3875c7'),
('RotationAllCases','compact44-rotation-coverage-prototype/RotationAllCases.lean','a09b6d055b','e99b3fff2266b5303bc18d09fb1781ae719354cc4650f1cc6ad9e5802374d259'),
('RotationIndexBounds','compact44-rotation-index-bounds-prototype/RotationIndexBounds.lean','d0059a99e8','87d0baeb7659ee26733f3014b5fdf1fadbe170a4b3477e8da1ae5335f7ec166b'),
('RotationCoverageBounded','compact44-rotation-index-bounds-prototype/RotationCoverageBounded.lean','d0059a99e8','ce88ff3c8eb3fbad23eaeab655216913e2c9adf5d5fc5ed3d5ec0a7aa9cdb628'),
('RotationBoundedCases','compact44-rotation-index-bounds-prototype/RotationBoundedCases.lean','d0059a99e8','ea920895ee005dd3cfa277c2b1af675c0b9e11b887e2311cd0e218facd3acb26')]
rows=[];names={'DiophantineConsistency.'+x[0] for x in RAW};available=set();external=set()
for name,rel,commit,sha in RAW:
 p=BASE/rel;assert p.is_file() and H(p)==sha;blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 text=p.read_text();imports=[x[7:] for x in text.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
 for dep in imports:
  if dep not in available:assert dep not in names,('out of order',name,dep);external.add(dep)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':imports,'axiom_reports':reports});available.add('DiophantineConsistency.'+name)
assert external=={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.ArithmeticCyclicWord'}
def slots(stem):
 r={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file(),str(p);r[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:r[str(p)]=None
 return r
objects={};direct={};targets={};package={};prev=None
for side in ('author','peer'):
 lib=PARENT/side/'lib';xs={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(xs)==189
 current=[{'path':k,'sha256':H(v),'realpath':str(v.resolve())} for k,v in sorted(xs.items())];pairs=[(x['path'],x['sha256']) for x in current]
 if prev is not None:assert pairs==prev
 prev=pairs;objects[side]=current
 for dep in sorted(external):
  stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  z=slots(lib/Path(*row['module'].split('.')));assert all(x is None for x in z.values());targets.update(z)
stem=PACKAGE/'Init';assert Path(str(stem)+'.olean').is_file();package.update(slots(stem))
assert len(direct)==40 and len(targets)==280 and len(package)==10
print(json.dumps({'status':'PRELIMINARY_ROTATION_WINDOWS_SOURCE_CLOSURE_NOT_A_BUILD','parent_audit_sha256':H(AUDIT/'CHECK.json'),'parent_receipt_sha256':a['receipt_sha256'],'source_order':rows,'parent_objects':objects,'external_direct_slots':direct,'target_slots':targets,'package_slots':package,'scope':'Point-in-time source/provider inventory only; no paired build, graph-selected source-index bound, strict-half temporal digit bound, retained-byte binding, clean column, decoder, machine or internal iPRA theorem.'},indent=2,sort_keys=True))
