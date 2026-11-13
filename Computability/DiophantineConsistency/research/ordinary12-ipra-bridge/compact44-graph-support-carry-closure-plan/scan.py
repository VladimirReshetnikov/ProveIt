#!/usr/bin/env python3
"""Point-in-time same-side fixed graph support/carry closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';AUDIT=ROOT/'Computability/DiophantineConsistency/reviews/compact44-rotation-windows-pair-independent-audit';PARENT=Path('/tmp/ipra-rotation-windows-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
assert H(AUDIT/'CHECK.json')=='7adb39a15c385f542ff5b8c34db7237a7edff25822d4e49aebdd104689745df0' and H(AUDIT/'terminal-observation.json')=='e3c13a07d3b4a37b96f02df3aee6e1d2d67f660fd84f93c71608eca3b7264e71'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT' and a['receipt_sha256']=='87bd0f6934145714f41f18e339f66b325bcb90f3da8fc44402ce3ff21b3d1e4d' and a['overlay_objects_per_side']==203 and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
RAW=[
('CompactSymbolicGraphSaturation','compact44-symbolic-saturation-prototype/CompactSymbolicGraphSaturation.lean','0ba22c687e','812a757a038d63873ad94a02c310c79800f1ed98abd18b6fe1cd17445b556e8a'),
('CompactSameWitnessSaturation2','compact44-same-witness-saturation-prototype/CompactSameWitnessSaturation2.lean','b3c898e2c4','246e900e939b0c6b6cbdc15f49eccc6bd07361c9816d099004ad59c79edb6afd'),
('CompactPositionIncrement','compact44-position-carry-prototype/CompactPositionIncrement.lean','ecafb6225a','38c19700d6caeadd28bae9d239b0c2302e032ec01011071ea4b4ace52543a675'),
('CompactPositionGraph','compact44-position-carry-prototype/CompactPositionGraph.lean','ecafb6225a','23ede19121f1691051f8667833b99baf09090af765ecc88c2357a74501cb715c'),
('CleanGeometry','compact44-clean-phase-geometry-prototype/CleanGeometry.lean','d90510c1bd','945102513c41d9202522316be9f87866198b2c40b441e675307d14f1832a792c'),
('CleanMaskClasses','compact44-clean-model-support-prototype/CleanMaskClasses.lean','1cf265fb8f','ac75423c2ac905fa533935e0284abaf229f0eab916eec43d34bbfe7911459598'),
('CleanModelSupport','compact44-clean-model-support-prototype/CleanModelSupport.lean','1cf265fb8f','a8c213ca7983521014f84a084ab39e9cda59fbee2c47d59e86127740f7e44bfe'),
('FixedGraphSupportCarry','compact44-fixed-graph-support-carry-prototype/FixedGraphSupportCarry.lean','9403a827c7','1d888e710123389065785919d6738921d55c8a917970bde06eb1a637b05d9584')]
rows=[];names={'DiophantineConsistency.'+x[0] for x in RAW};available=set();external=set()
for name,rel,commit,sha in RAW:
 p=BASE/rel;assert p.is_file() and H(p)==sha;blob=subprocess.run(['git','show',commit+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==sha
 text=p.read_text();imports=[x[7:] for x in text.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
 for dep in imports:
  if dep not in available:assert dep not in names,('out of order',name,dep);external.add(dep)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'source_commit':commit,'source_sha256':sha,'imports':imports,'axiom_reports':reports});available.add('DiophantineConsistency.'+name)
assert external=={'DiophantineConsistency.FreeJConcreteDigitsClient','DiophantineConsistency.CompactLowExact','DiophantineConsistency.CompactLowEven','DiophantineConsistency.CompactHighResidue','DiophantineConsistency.FreeJGraphCongruenceExplore','DiophantineConsistency.CompactMixedIncrement','DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.CompactSymbolicPorts','DiophantineConsistency.CompactConcreteMask','DiophantineConsistency.CompactDummyBound','DiophantineConsistency.FixedGraphIndexedCarry'}
def slots(stem):
 r={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):assert p.is_file(),str(p);r[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:r[str(p)]=None
 return r
objects={};direct={};targets={};package={};prev=None
for side in ('author','peer'):
 lib=PARENT/side/'lib';xs={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(xs)==203
 current=[{'path':k,'sha256':H(v),'realpath':str(v.resolve())} for k,v in sorted(xs.items())];pairs=[(x['path'],x['sha256']) for x in current]
 if prev is not None:assert pairs==prev
 prev=pairs;objects[side]=current
 for dep in sorted(external):
  stem=lib/Path(*dep.split('.'));assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 for row in rows:
  z=slots(lib/Path(*row['module'].split('.')));assert all(x is None for x in z.values());targets.update(z)
stem=PACKAGE/'Init';assert Path(str(stem)+'.olean').is_file();package.update(slots(stem))
assert len(direct)==220 and len(targets)==160 and len(package)==10
print(json.dumps({'status':'PRELIMINARY_FIXED_GRAPH_SUPPORT_CARRY_SOURCE_CLOSURE_NOT_A_BUILD','parent_audit_sha256':H(AUDIT/'CHECK.json'),'parent_receipt_sha256':a['receipt_sha256'],'source_order':rows,'parent_objects':objects,'external_direct_slots':direct,'target_slots':targets,'package_slots':package,'scope':'Point-in-time source/provider inventory only; no paired build, selected clean predecessor, fractional half-radix digit bound, retained-byte K binding, full decoder, machine or internal iPRA theorem.'},indent=2,sort_keys=True))
