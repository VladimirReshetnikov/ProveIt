#!/usr/bin/env python3
"""Point-in-time source and object closure for the symbolic graph-digit client."""
import hashlib,json,os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];BASE=ROOT/'research/ordinary12-ipra-bridge'
PREFIX=Path('/tmp/ipra-freej-concrete-digits-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDITS={
 ROOT/'reviews/ordinary12-freej-concrete-digits-client-independent-audit/CHECK.json':('5ef4ae700c1105220472fe57952929071a6c5666d1cad01a3b37c971c49d3056','PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_CLIENT_AUDIT'),
 ROOT/'reviews/compact44-low-exact-independent-audit/CHECK.json':('f928e70299e53116fdcd786a31fe6d04db362c75e90f77b14ed0db498340a6c4','PASS_INDEPENDENT_COMPACT44_LOW_EXACT_AUDIT'),
 ROOT/'reviews/compact44-high-population-independent-audit/CHECK.json':('074d5c92e0394a5b67c337e3cb89694e43a8ec47778b0b38ad814b3b7f7c281c','PASS_INDEPENDENT_COMPACT44_HIGH_POPULATION_AUDIT'),
 ROOT/'reviews/compact44-high-residue-independent-audit/CHECK.json':('9bfc8a51bc57d821da3103d1c42536fbdc5867f6aeb6a9e77b4e672af9c61ad6','PASS_INDEPENDENT_COMPACT44_HIGH_RESIDUE_AUDIT')}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,(h,status) in AUDITS.items():
 if H(p)!=h or json.loads(p.read_text()).get('status')!=status:raise ValueError(('audit drift',str(p)))
sources={}
for loc in (ROOT/'Lean/DiophantineConsistency',BASE):
 for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
selected={k:BASE/v for k,v in {
 'CompactLowPopulation':'compact44-low-population-exact-prototype/CompactLowPopulation.lean',
 'CompactSupportCard':'compact44-low-population-exact-prototype/CompactSupportCard.lean',
 'CompactLowExact':'compact44-low-population-exact-prototype/CompactLowExact.lean',
 'CompactLowEven':'compact44-low-even-prototype/CompactLowEven.lean',
 'CompactHighPopulation':'compact44-high-population-prototype/CompactHighPopulation.lean',
 'CompactHighResidue':'compact44-high-residue-prototype/CompactHighResidue.lean',
 'CompactSymbolicGraphDigits':'compact44-symbolic-graph-join-prototype/CompactSymbolicGraphDigits.lean'}.items()}
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
 go('DiophantineConsistency.CompactSymbolicGraphDigits')
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
 'CompactLowPopulation':'b4b052b87a8883bc5f8096aca1eb1416583a51bda277c6eee95d973f018ed32b',
 'CompactSupportCard':'654b825840ffdd9deda64f6ad608d707231bae9c09b6d7d8ad125467493b73e8',
 'CompactLowExact':'189d3a0d400409b26595cdaa1a7aeacf99285481cb91827d2a4f89dd769018f6',
 'CompactLowEven':'ae40037d5611824ad3a8b39c3b378b18e61fff82852af0dbc11eeb8960641499',
 'CompactHighPopulation':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
 'CompactHighResidue':'2e4da7f6de540be280f37214ee0f9ab8272636afff515c2a5ee6992851b6565a',
 'CompactSymbolicGraphDigits':'7c8524757c85a35c058329009bf982ce542a168c6b128bd9b64ec46fd10a2f9e'}
if {r['module'].split('.')[-1]:r['source_sha256'] for r in x}!=expected_sources:raise ValueError('unexpected closure or selected source drift')
choices={k:{'selected':str(p),'selected_sha256':H(p),'all_candidates':[{'path':str(q),'sha256':H(q)} for q in sorted(sources.get(k,[]))]} for k,p in selected.items()}
result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','parent_audits':{str(p):h for p,(h,_) in AUDITS.items()},'inherited_objects':objects,'explicit_choices':choices,'modules':x,'scope':'Point-in-time source/import and object scan; uncompiled client, no simultaneous freeze, coherent build, graph-port calibration, checker, package/dynamic ancestry or PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
