#!/usr/bin/env python3
"""Point-in-time 21-source graph/band same-side closure scan; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';OLD=BASE/'compact44-direct-k-band-join-plan';PARENT=Path('/tmp/ipra-direct-symbolic-k-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
assert H(OLD/'scan.json')=='2048ee458a2f49755858e991e3837b71aab244ce9c8521e483e6cdea6282616d'
r=subprocess.run([sys.executable,'-I','-S','-B',str(OLD/'scan.py')],cwd=ROOT,capture_output=True,timeout=300);assert r.returncode==0 and not r.stderr and r.stdout==(OLD/'scan.json').read_bytes(),('base scan',r.returncode,r.stderr)
base=json.loads(r.stdout);rows=base['source_order']; assert len(rows)==14
extras=[
('TwoBand','compact44-two-band-rotation-prototype/TwoBand.lean','d71872eb82','6bf2dc0cf02bc32ccff07cc5cc3b66f271fc86bed01dfc151a07f39893a48908'),
('KCast','compact44-k-cast-pieces-prototype/KCast.lean','be6e0abf51','e5007b38c1847e56d4b14846ae2583d9fc135b66fa7b9cf4b0db1e93aeb64e7a'),
('SymbolicKBandDraft','compact44-symbolic-k-band-cast-prototype/SymbolicKBandDraft.lean','d8b0786d8c','3b1edf6b242a1f5a8f93bb308a794418e1f7bc87dc803b295644bdbd384f0ffc'),
('ModelBandCut','compact44-model-band-cut-prototype/ModelBandCut.lean','2272e60145','fc3ea719b09c81e8bce78df1ce6898774900bf4b214bbc787adb4432970208b3'),
('FreeJGraphCongruenceExplore','free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean','f3afbc380f','d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0'),
('GenericGraphBand','compact44-graph-band-client-prototype/GenericGraphBand.lean','7d43e9f77c','6f9cd861b3279aecdf952e0517ef83cc5bc02ad9734108a159e88c0e52ebd31e'),
('SymbolicGraphBand','compact44-graph-band-client-prototype/SymbolicGraphBand.lean','7d43e9f77c','7de9bc84b0dc6dd177c50ed652055a54b696b1f4b750ad75e63b85d485d7a285')]
for name,rel,commit,sha in extras:
 p=BASE/rel;assert p.is_file() and H(p)==sha;blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 text=p.read_text();rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':[x[7:] for x in text.splitlines() if x.startswith('import ')],'axiom_reports':re.findall(r'^#print axioms\s+(\S+)',text,re.M)})
names={x['module'] for x in rows};available=set();external=set()
for row in rows:
 for dep in row['imports']:
  if dep not in available:assert dep not in names,('out of order',row['module'],dep);external.add(dep)
 available.add(row['module'])
assert external=={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.Compact943Data','DiophantineConsistency.CompactCoefficientMass','DiophantineConsistency.CompactSymbolicKernelOpaque','DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.ArithmeticModularCancellation','Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Algebra.BigOperators.Fin'}
def slots(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file(),str(p);out[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:out[str(p)]=None
 return out
direct={};targets={};package={}
for side in ('author','peer'):
 lib=PARENT/side/'lib';assert len(list(lib.rglob('*.olean')))==150
 for dep in sorted(external):
  if dep.startswith('DiophantineConsistency.'):
   stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  z=slots(lib/Path(*row['module'].split('.')));assert all(x is None for x in z.values());targets.update(z)
for dep in sorted({'Init'}|{x for x in external if x.startswith('Mathlib.')}):
 stem=PACKAGE/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();package.update(slots(stem))
assert len(direct)==120 and len(targets)==420 and len(package)==30
print(json.dumps({'status':'PRELIMINARY_GRAPH_BAND_21_SOURCE_CLOSURE_NOT_A_BUILD','base_scan_sha256':H(OLD/'scan.json'),'parent_audit_sha256':base['parent_audit_sha256'],'source_order':rows,'parent_objects':base['parent_objects'],'divergent_overlap':base['divergent_overlap'],'external_direct_slots':direct,'target_slots':targets,'package_slots':package,'scope':'Point-in-time source/provider inventory only; no paired build, retained-byte K binding, fractional rotation, full graph column, machine equivalence or internal iPRA theorem.'},indent=2,sort_keys=True))
