#!/usr/bin/env python3
"""Point-in-time source and object scan for the concrete-digit join."""
import hashlib,json,os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];BASE=ROOT/'research/ordinary12-ipra-bridge'
PREFIX=Path('/tmp/ipra-freej-saturation-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=ROOT/'reviews/ordinary12-freej-saturation-client-independent-audit/CHECK.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if H(AUDIT)!='847f3e467e93d871087695ee3c66f8042c22767a7d43ec1a14973cffe6ee043f':raise ValueError('parent audit drift')
check=json.loads(AUDIT.read_text())
if check.get('status')!='PASS_INDEPENDENT_FREEJ_SATURATION_CLIENT_AUDIT' or check.get('recorded_outer_exit')!=0:raise ValueError('invalid saturation audit')
sources={}
for loc in (ROOT/'Lean/DiophantineConsistency',BASE):
 for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
selected={'CompactDummyBound':BASE/'compact44-dummy-bound-prototype/CompactDummyBound.lean','CompactMaskSlot':BASE/'compact44-mask-slot-prototype/CompactMaskSlot.lean'}
def scan(base):
 seen=set();order=[]
 def go(name):
  if name in seen:return
  seen.add(name);rel=Path(*name.split('.')).with_suffix('.olean')
  if (base/rel).is_file() or (PACKAGE/rel).is_file():return
  stem=name.split('.')[-1];matches=[selected[stem]] if stem in selected else sources.get(stem,[])
  if len(matches)!=1:raise ValueError(('missing or ambiguous source',name,[str(p) for p in matches]))
  p=matches[0];imports=[v for line in p.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  for v in imports:go(v)
  order.append({'module':name,'source':str(p),'source_sha256':H(p),'imports':imports})
 go('DiophantineConsistency.CompactConcreteIncrement')
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
choices={k:{'selected':str(p),'selected_sha256':H(p),'all_candidates':[{'path':str(q),'sha256':H(q)} for q in sorted(sources[k])]} for k,p in selected.items()}
result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','parent_audit_path':str(AUDIT),'parent_audit_sha256':H(AUDIT),'inherited_objects':objects,'explicit_choices':choices,'modules':x,'scope':'Point-in-time source/import and object observation; no simultaneous freeze, Lean build, package/dynamic ancestry, retained-port binding, graph instantiation, or PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
