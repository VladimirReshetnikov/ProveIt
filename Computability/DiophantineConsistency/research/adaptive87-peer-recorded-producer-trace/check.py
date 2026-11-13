#!/usr/bin/env python3
"""Read-only recorded-edge scan. This is not a Lean or full import audit."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent
pins=json.loads((D/'pins.json').read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():
 q=Path(p) if p.startswith('/') else R/p
 assert sha(q)==h,p
objs=json.loads((R/'research/adaptive87-four-square-peer-provider-inventory/result.json').read_text())['objects']
m=json.loads((R/'reviews/ipra-adaptive-native-fixed-continuation/manifest.json').read_text()); records={}
def add(n,h,label,deps,exitcode):
 assert exitcode==0,(label,n)
 key=(n,h)
 if key not in records: records[key]=(label,deps)
for label,p in [('repaired-peer','reviews/ipra-current-repaired-build-verification/independent-state.json'),('ancestry-repair','/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/state.json'),('fixed','reviews/ipra-adaptive-native-fixed-continuation-verification/author-state.json')]:
 q=Path(p) if p.startswith('/') else R/p; state=json.loads(q.read_text());assert state['status']=='PASS'
 for r in state['records']:add(r['name'],r['object_sha256'],label,{i:v['sha256'] for i,v in r['direct_imports'].items()},r['exit'])
for k in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 for n,r in m[k].items():add(n,r['object_sha256'],k,{i:v['sha256'] for i,v in r['direct_imports'].items()},r['exit'])
h=json.loads((R/'reviews/ha87-isolated-full-author-pass/state.json').read_text());assert h['status']=='PASS'
for r in h['records']:add(r['module'],r['object_sha256'],'ha-author',r['dependency_hashes'],r['exit'])
s=json.loads(Path('/tmp/ipra-rank17-native-n795r_ja/state.json').read_text());assert s['status']=='PASS'
for r in s['records']:
 deps={}
 for p,v in r['direct_inputs'].items():
  if '/DiophantineConsistency/' in p and p.endswith('.olean'):
   deps['DiophantineConsistency.'+p.split('/DiophantineConsistency/',1)[1][:-6].replace('/','.')]=v['sha256']
 add('DiophantineConsistency.'+r['module'],r['object_sha256'],'rank17-direct-inputs-project-only',deps,r['exit'])
root=Path('/tmp/nine-ipra-guarded-peer-20261102-a/lib')
def observed(n):
 p=root/Path(n.replace('.','/')+'.olean')
 if not p.is_file():return None
 return {'path':str(p.resolve()),'sha256':sha(p),'in_658':n in objs}
roots=['DiophantineConsistency.HAAdaptiveFactor87','DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.HAExpressionSameZero','DiophantineConsistency.PRAPositiveCode']
seen={}; edges=[]; frontier=[]; external=set();stack=roots[:]
while stack:
 n=stack.pop()
 if n in seen: continue
 obj=observed(n);assert obj is not None,n
 if n in objs:assert obj['sha256']==objs[n]['object_sha256'] and obj['path']==objs[n]['resolved'],n
 item=records.get((n,obj['sha256']));seen[n]=dict(obj,producer=item[0] if item else None)
 if not item: frontier.append(n);continue
 for dep,want in item[1].items():
  if not dep.startswith('DiophantineConsistency.'):external.add(dep);continue
  got=observed(dep)
  edge={'from':n,'to':dep,'recorded':want,'selected':got and got['sha256'],'matches':got is not None and got['sha256']==want}
  edges.append(edge)
  if edge['matches']:stack.append(dep)
# Preserve any contradiction rather than asserting it away.
mismatches=[e for e in edges if not e['matches']]
assert seen['DiophantineConsistency.HAAdaptiveFactor87']['sha256']=='33e6b87c1a662b9c56facccb7fec4c7655d3924d5725bd904ed211248c03343c'
assert seen['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']['sha256']=='e357624f5ab38852b316b0b492050dbc1ae4c0f90c90fc8cb0481c9061529f65'
assert seen['DiophantineConsistency.HAExpressionSameZero']['sha256']=='f2ac7b385fed5645a5af625da3c7aacbe57613521258a8854c46fdf7f4754755'
assert any(e['from']=='DiophantineConsistency.HAExpressionSameZero' and e['to']=='DiophantineConsistency.HAAdaptiveDirectOrdinate86' and e['matches'] for e in edges)
assert seen['DiophantineConsistency.PRAPositivePackedNormal']['sha256']=='54828cd4b3f726ef5d93485f2127f83a85e9812145d1aa36b3854173d2032d4e'
assert any(e['from']=='DiophantineConsistency.PRAPositivePackedNormal' and e['to']=='DiophantineConsistency.PRAPositiveMapPack' and e['recorded']=='5902bb1a9c0f0d77849cb5843ddcc35f3e3b7b248e12773e0bba23d7bc26f505' and e['matches'] for e in edges)
origins=json.loads((R/'reviews/ipra-frozen-repair-plan-v2-source-origin-audit/source-nodes.json').read_text())
origin_keys=set(origins)
origin_matches=sorted(n for n,v in seen.items() if n+'|'+v['sha256']+'|'+v['path'] in origin_keys)
frontier_origin_matches=sorted(n for n in frontier if n in origin_matches)
print(json.dumps({'scope':'recorded project edges only; package and dynamic closure excluded','roots':roots,'source_origin_matches':origin_matches,'frontier_source_origin_matches':frontier_origin_matches,'seen':seen,'edge_count':len(edges),'mismatches':mismatches,'missing_record':sorted(frontier),'external_names':sorted(external),'not_in_658':sorted(n for n,v in seen.items() if not v['in_658'])},sort_keys=True,indent=2))
