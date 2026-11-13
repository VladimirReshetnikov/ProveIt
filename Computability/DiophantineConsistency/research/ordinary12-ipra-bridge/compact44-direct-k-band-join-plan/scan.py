#!/usr/bin/env python3
"""Point-in-time candidate rebuild frontier over direct-K provider; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';AUDIT=BASE/'reviews/compact44-direct-symbolic-k-pair-independent-audit';PARENT=Path('/tmp/ipra-direct-symbolic-k-pair-01');OTHER=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
ROWS=[
('ArithmeticCyclicWord','Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticCyclicWord.lean','5fcc0384fe','ed29e5d553cc159084a8fdeec3baa0c23c097b27d666fa8ad04a2a680749dbee',['DiophantineConsistency.ArithmeticWindowDigits','Mathlib.Algebra.BigOperators.Ring.Finset']),
('ArithmeticWindowCarry','Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticWindowCarry.lean','c78ee90e4b','b89c8fcface92fa9e16d45ae50463b557a41254841a4fa9586207244fa8ec25b',['DiophantineConsistency.ArithmeticCyclicWord']),
('CompactSelector','compact44-selector-prototype/CompactSelector.lean','bea685c46d','4a85f7f526cbc2aef8b97c3246a5a10e13be705ae32e1a70a3221043a42fcc06',['DiophantineConsistency.ArithmeticWindowDigits']),
('CompactSelectorDiv','compact44-selector-div-prototype/CompactSelectorDiv.lean','a44a25113d','6fa8d26a7f898730a27911003fe95914551672b41f0414ccfba964d670f1aaf7',['DiophantineConsistency.CompactSelector']),
('CompactCopy','compact44-copy-prototype/CompactCopy.lean','4fcbaa5145','6223d85150d8f40fc02585804e8755461c77f7d7e3e25d9c89abc4c424cdf6a1',['DiophantineConsistency.ArithmeticWindowDigits']),
('CompactSelectorSum','compact44-selector-sum-prototype/CompactSelectorSum.lean','bd82dfcc4a','814259bc45d143dca0e4c310c02c1f0a26dba27294dc6dcdf4d0f032ba661a5f',['DiophantineConsistency.ArithmeticWindowDigits']),
('CompactSelectorDecoder','compact44-selector-decoder-prototype/CompactSelectorDecoder.lean','2ad42e3c7d','96ba4a6ca5855ec86698b1f7fb2fecf4deeeb4fe5df04bb923cc0203242fe970',['DiophantineConsistency.CompactSelectorDiv','DiophantineConsistency.CompactCopy','DiophantineConsistency.CompactSelectorSum']),
('CompactSelectorConverse','compact44-mask-converse-prototype/CompactSelectorConverse.lean','72040220e5','6f031e3936e748739b016188f26702c1f1361c11b99cf179349b92b542fcf632',['DiophantineConsistency.ArithmeticWindowDigits']),
('CompactDecoderIff','compact44-decoder-iff-prototype/CompactDecoderIff.lean','842f77f47a','10b6636d29e19d2171035537d14bf8d709b7643ff2c0a71bc4ab490355832962',['DiophantineConsistency.CompactSelectorDecoder','DiophantineConsistency.CompactSelectorConverse']),
('CompactTilePayload','compact44-tile-payload-prototype/CompactTilePayload.lean','cfeef02268','05f1cc02e25fe2d44a5b2fd65859c03677b86e0ddcfa0d4c807d413986fb5410',['DiophantineConsistency.ArithmeticWindowDigits']),
('Compact943Decoder','compact44-943-decoder-prototype/Compact943Decoder.lean','a559988b8a','b86cef78ba82bb77e3a5c4f4c5dafeb719f7b8e802ff0527ef31dca4bc62271f',['DiophantineConsistency.Compact943Data','DiophantineConsistency.CompactTilePayload','DiophantineConsistency.CompactDecoderIff']),
('CompactCoefficientDecoder','compact44-coefficient-decomposition-prototype/CompactCoefficientDecoder.lean','d417147fec','86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8',['DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.Compact943Decoder','DiophantineConsistency.CompactCoefficientMass']),
('CompactPartialBand','compact44-partial-band-prototype/CompactPartialBand.lean','7dea2a8f40','26b73b92c91baef599ab9d473965af940b9b39ae81d76f0979ed80129109ba0f',['DiophantineConsistency.CompactCoefficientDecoder','DiophantineConsistency.ArithmeticCyclicWord']),
('CompactPartialBandRotation','compact44-partial-band-rotation-prototype/CompactPartialBandRotation.lean','6fde7b8487','a74f981ea103fabce4163336233071018bbba7a445db05a67ee7207af8cc1438',['DiophantineConsistency.CompactPartialBand'])]
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(AUDIT/'CHECK.json')=='5aecb3c05962fd5f13650899bac9ce6f2406827a8d08f43714ddd2966716a634' and H(AUDIT/'terminal-observation.json')=='51feb6dba903581ab36824efa3c816a4b4e6c2d8b44d63030e0971acf82f73a3'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT' and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
names={'DiophantineConsistency.'+x[0] for x in ROWS};available=set();external=set();rows=[]
for name,rel,commit,sha,imports in ROWS:
 p=ROOT/rel if rel.startswith('Computability/') else RESEARCH/rel;assert p.is_file() and H(p)==sha
 blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 actual=[x[7:] for x in p.read_text().splitlines() if x.startswith('import ')];assert actual==imports
 reports=re.findall(r'^#print axioms\s+(\S+)',p.read_text(),re.M)
 for dep in imports:
  if dep not in available:
   assert dep not in names,('out of order',name,dep);external.add(dep)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':imports,'axiom_reports':reports});available.add('DiophantineConsistency.'+name)
assert external=={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.Compact943Data','DiophantineConsistency.CompactCoefficientMass','Mathlib.Algebra.BigOperators.Ring.Finset'}
snapshot=Path('/tmp/ipra-thirteen-current-source-02');assert H(snapshot/'manifest.json')=='2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3'
for row in rows[:2]:assert H(snapshot/'src/DiophantineConsistency'/Path(row['source']).name)==row['source_sha256']

def slots(stem):
 r={}
 for suf in SUFFIXES:
  p=Path(str(stem)+suf)
  if os.path.lexists(p):
   assert p.is_file(),str(p);r[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:r[str(p)]=None
 return r
objects={};direct={};targets={};comparison={};prior=None
for side in ('author','peer'):
 lib=PARENT/side/'lib';other=OTHER/side/'lib';xs={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};ys={p.relative_to(other).as_posix():p for p in other.rglob('*.olean') if p.is_file()};assert len(xs)==150 and len(ys)==126
 current=[{'path':k,'sha256':H(v),'realpath':str(v.resolve())} for k,v in sorted(xs.items())];pairs=[(x['path'],x['sha256']) for x in current]
 if prior is not None:assert pairs==prior
 prior=pairs;objects[side]=current
 diff=[{'path':x,'direct_k_sha256':H(xs[x]),'coefficient_sha256':H(ys[x])} for x in sorted(xs.keys()&ys.keys()) if H(xs[x])!=H(ys[x])];assert len(xs.keys()&ys.keys())==90 and {x['path'] for x in diff}=={'DiophantineConsistency/'+x+'.olean' for x in ('ArithmeticBinaryCarry','ArithmeticBinomLegendre','Compact943Data','CompactCoefficientMass')};comparison[side]=diff
 for dep in sorted(external):
  if dep.startswith('DiophantineConsistency.'):
   stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  stem=lib/Path(*row['module'].split('.'));z=slots(stem);assert all(v is None for v in z.values());targets.update(z)
package_slots={}
for dep in ('Init','Mathlib.Algebra.BigOperators.Ring.Finset'):
 stem=PACKAGE/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();package_slots.update(slots(stem))
assert len(direct)==60 and len(targets)==280 and len(package_slots)==20
print(json.dumps({'status':'PRELIMINARY_DIRECT_K_PARTIAL_BAND_JOIN_NOT_A_BUILD','parent_audit_sha256':H(AUDIT/'CHECK.json'),'historical_window_manifest_sha256':H(snapshot/'manifest.json'),'source_order':rows,'parent_objects':objects,'divergent_overlap':comparison,'external_direct_slots':direct,'target_slots':targets,'package_slots':package_slots,'scope':'Point-in-time candidate same-side rebuild only; no source/object transitive authentication, parent rerun, Lean build, actual hK cast, retained-byte binding, full graph-column or iPRA proof.'},indent=2,sort_keys=True))
