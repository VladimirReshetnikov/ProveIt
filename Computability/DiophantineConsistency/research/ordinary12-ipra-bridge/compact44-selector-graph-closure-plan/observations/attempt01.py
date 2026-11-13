#!/usr/bin/env python3
"""Point-in-time four-source selector closure; no Lean compilation."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge'
AUDIT=BASE/'reviews/compact44-same-witness-saturation-independent-audit';PARENT=Path('/tmp/ipra-same-witness-saturation-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
ROWS=[
 ('CompactPositionIncrement','compact44-position-carry-prototype/CompactPositionIncrement.lean','ecafb6225a','38c19700d6caeadd28bae9d239b0c2302e032ec01011071ea4b4ace52543a675',['CompactMixedIncrement'],['CompactPositionCarry.increment_digits']),
 ('CompactPositionGraph','compact44-position-carry-prototype/CompactPositionGraph.lean','ecafb6225a','23ede19121f1691051f8667833b99baf09090af765ecc88c2357a74501cb715c',['CompactSameWitnessSaturation2','CompactPositionIncrement'],['CompactPositionCarry.generic_position_noCarry','CompactPositionCarry.fixed_position_noCarry']),
 ('CompactSelectorMask','compact44-selector-mask-class-prototype/CompactSelectorMask.lean','cfa2403812','91846742919ca2a0d3ffce3a6da0b7cac2044de2d9ef6fc6b640c329431df550',['CompactPositionGraph'],['CompactSelectorMask.selector_mask_digit','CompactSelectorMask.absent_mask_digit']),
 ('CompactSelectorGraph','compact44-selector-graph-prototype/CompactSelectorGraph.lean','e90ea00818','dfd3155e95af8d17e6ee46a3eb37d0f40a8ad429febb1caf23dae8f2a1bc447b',['CompactSelectorMask'],['CompactSelectorGraph.selector_slot','CompactSelectorGraph.excluded_slot','CompactSelectorGraph.fixed_graph_selector_bounds'])]
AH='5d8c620fc76d741a7d1b398f9e442ce7dfea83a90cd39a42c53e9320d75dd754';OH='109b331fc4e435f4a59fa63fceb909c49057f82b8542131a9adec8eac8ff4915'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def slots(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_file(),'invalid slot '+str(p));out[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:out[str(p)]=None
 return out
need(H(AUDIT/'CHECK.json')==AH and H(AUDIT/'terminal-observation.json')==OH,'parent audit pins');a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes())
need(a['status']=='PASS_INDEPENDENT_SAME_WITNESS_PAIR_ARTIFACT_AUDIT' and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['check_sha256']==AH and o['lean_launched'] is False,'parent audit observation')
sources=[]
for module,rel,commit,sha,imports,names in ROWS:
 src=RESEARCH/rel;need(H(src)==sha,'source '+module);blob=subprocess.run(['git','show',commit+':'+src.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout;need(hashlib.sha256(blob).hexdigest()==sha,'source commit '+module)
 actual=[line[7:] for line in src.read_text().splitlines() if line.startswith('import ')];need(actual==['DiophantineConsistency.'+x for x in imports],'imports '+module)
 reports=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M);need(reports==names,'report names '+module)
 sources.append({'module':'DiophantineConsistency.'+module,'source':str(src),'source_commit':commit,'source_sha256':sha,'imports':actual,'axiom_reports':reports})
libs=[PARENT/x/'lib' for x in ('author','peer')];inv=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs]
need(set(inv[0])==set(inv[1]) and len(inv[0])==146,'paired inventory paths');objects=[]
for rel in sorted(inv[0]):
 a,b=inv[0][rel],inv[1][rel];need(H(a)==H(b),'paired object '+rel);objects.append({'path':rel,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
direct={};targets={}
for side,lib in zip(('author','peer'),libs):
 available={str(p.with_suffix('')).replace('/','.') for p in inv[0]}
 for module,_,_,_,imports,_ in ROWS:
  for dep in imports:need('DiophantineConsistency.'+dep in available,('missing topological same-side import',side,module,dep))
  stem=lib/'DiophantineConsistency'/module;st=slots(stem);need(all(v is None for v in st.values()),('target occupied',side,module));targets.update(st);available.add('DiophantineConsistency.'+module)
 for module in ('CompactMixedIncrement','CompactSameWitnessSaturation2'):
  stem=lib/'DiophantineConsistency'/module;need(Path(str(stem)+'.olean').is_file(),'missing external '+str(stem));direct.update(slots(stem))
init=PACKAGE/'Init.olean';need(init.is_file(),'missing Init');init_slots=slots(PACKAGE/'Init')
for module,rel,_,sha,_,_ in ROWS:need(H(RESEARCH/rel)==sha,'source post-read '+module)
print(json.dumps({'status':'PRELIMINARY_COMPACT_SELECTOR_GRAPH_CLOSURE_NOT_A_BUILD','source_order':sources,'parent_audit_sha256':AH,'objects':objects,'external_direct_companion_slots':direct,'target_companion_slots':targets,'package_init_companion_slots':init_slots,'scope':'Point-in-time four-source selector closure on paired same-witness provider; no parent rerun or build, complete package/transitive/dynamic ancestry, retained-port binding, decoder, machine or internal iPRA proof.'},indent=2,sort_keys=True))
