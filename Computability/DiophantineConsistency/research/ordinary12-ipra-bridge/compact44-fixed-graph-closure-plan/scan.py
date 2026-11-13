#!/usr/bin/env python3
"""Point-in-time source/import closure for fixed symbolic graph digits."""
import hashlib,json,os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];BASE=ROOT/'research/ordinary12-ipra-bridge'
PREFIX=Path('/tmp/ipra-compact-symbolic-graph-join-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=ROOT/'reviews/compact44-symbolic-graph-join-independent-audit/CHECK.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if H(AUDIT)!='3164ef421742c093b07fb1ff491c19d9586f2ff19f83d2371f3311b4958721ec':raise ValueError('parent audit drift')
check=json.loads(AUDIT.read_text())
if check.get('status')!='PASS_INDEPENDENT_SYMBOLIC_GRAPH_JOIN_PAIR_AUDIT' or check.get('recorded_outer_exit')!=0:raise ValueError('invalid symbolic join audit')
sources={}
for loc in (ROOT/'Lean/DiophantineConsistency',BASE):
 for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
selected={k:BASE/v for k,v in {
 'CompactMaskBounds':'compact44-mask-bounds-prototype/CompactMaskBounds.lean',
 'CompactBetaResidues':'compact44-mask-bounds-finish-prototype/CompactBetaResidues.lean',
 'CompactMaskBoundFinish':'compact44-mask-bounds-finish-prototype/CompactMaskBoundFinish.lean',
 'CompactFixedBeta':'compact44-fixed-beta-bounds-prototype/CompactFixedBeta.lean',
 'CompactSymbolicPorts':'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean',
 'CompactGenericGraphDigits':'compact44-fixed-graph-digits-prototype/CompactGenericGraphDigits.lean'}.items()}
def scan(lib):
 seen=set();order=[]
 def go(name):
  if name in seen:return
  seen.add(name);rel=Path(*name.split('.')).with_suffix('.olean')
  if (lib/rel).is_file():return
  if not name.startswith('DiophantineConsistency.') and (PACKAGE/rel).is_file():return
  stem=name.split('.')[-1];matches=[selected[stem]] if stem in selected else sources.get(stem,[])
  if len(matches)!=1 or not matches[0].is_file():raise ValueError(('missing or ambiguous source',name,[str(p) for p in matches]))
  p=matches[0];imports=[v for line in p.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  for v in imports:go(v)
  order.append({'module':name,'source':str(p),'source_sha256':H(p),'imports':imports})
 go('DiophantineConsistency.CompactGenericGraphDigits')
 return order
a=PREFIX/'author/lib';b=PREFIX/'peer/lib';aa={p.relative_to(a):p for p in a.rglob('*.olean')};bb={p.relative_to(b):p for p in b.rglob('*.olean')}
if aa.keys()!=bb.keys():raise ValueError('provider object sets differ')
objects=[]
for rel in sorted(aa):
 h=H(aa[rel])
 if H(bb[rel])!=h:raise ValueError(('provider object drift',str(rel)))
 objects.append({'module_path':str(rel),'sha256':h,'author_resolved_path':str(aa[rel].resolve()),'peer_resolved_path':str(bb[rel].resolve())})
x,y=scan(a),scan(b)
if x!=y:raise ValueError('side closure differs')
expected_sources={
 'CompactMaskBounds':'5e6f5d2942df9f496a9e5822ca73ef4fba6695a9ce55f264edad8fc29f1d5fcd',
 'CompactBetaResidues':'fa6f19df0cbdf34c60676a384fd02e1715ac8a91040c00c52c7878fe6fd5aa1e',
 'CompactMaskBoundFinish':'ceb23357a67239742819c33a25bce287bea5487d52cc554e392e6a16a203cd9d',
 'CompactFixedBeta':'9adc356351adfdeb2ccfcfe61cbf18fcd8a8458c911fabd91d07fe49ce85fcd5',
 'CompactSymbolicPorts':'0c2f2859c5420b3d22b73c3e5e72a7307a75d2b83d95d29eb7691f085d812148',
 'CompactGenericGraphDigits':'1c9b8a0e2f93d9d41c8483e66c148046f792a9e3e5bc52542d3743f41a1daa34'}
if {r['module'].split('.')[-1]:r['source_sha256'] for r in x}!=expected_sources:raise ValueError('unexpected closure or selected source drift')
choices={k:{'selected':str(p),'selected_sha256':H(p),'all_candidates':[{'path':str(q),'sha256':H(q)} for q in sorted(sources.get(k,[]))]} for k,p in selected.items()}
result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','parent_audit_path':str(AUDIT),'parent_audit_sha256':H(AUDIT),'inherited_objects':objects,'explicit_choices':choices,'modules':x,'scope':'Point-in-time source/import and object scan; no simultaneous freeze, paired build, retained-port calibration, checker, machine or PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
