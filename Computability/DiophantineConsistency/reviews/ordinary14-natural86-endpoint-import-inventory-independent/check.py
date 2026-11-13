#!/usr/bin/env python3
"""Independent static header/graph audit; does not call Lean."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-natural86-endpoint-import-inventory';B=D/'research/ordinary14-root74-endpoint-import-inventory'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'97b9fae77a9449f29fbad6609b51805645b5889561b58f35deef0cee786ba247',A/'check_source.py':'eb4ab66371ef5c06bc05287396f793ed4fd05b053353c322ae8b99bca43b2873',A/'inventory.json':'3ea586dd5f25b8230fa4cccee93e18bbb68ebc23beda8dfead8a9db060593732',B/'inventory.json':'2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'}
for p,h in pins.items():
 if p==A/'README.md':
  raw=p.read_bytes();tail=b'\nIndependent source review: [natural86 endpoint import inventory](../../reviews/ordinary14-natural86-endpoint-import-inventory-independent/README.md).\n'
  assert sha(p)=='c5fe711957ad48e974ce73167dc7dac717d68ea35e11c2f7b1887b6f41aff0f6' and raw.endswith(tail) and hashlib.sha256(raw[:-len(tail)]).hexdigest()==h
 else:assert sha(p)==h,(str(p),sha(p),h)
i=json.loads((A/'inventory.json').read_text());old=json.loads((B/'inventory.json').read_text())
rows=i['drafts_topological'];ext=i['qualified_direct_sources'];assert len(rows)==162 and len(ext)==36
index=defaultdict(list)
for p in (D/'research').rglob('*.lean'):index[p.stem].append(p)
by={r['module']:r for r in rows};assert len(by)==len(rows)
def header(p):
 out=[]
 for line in p.read_text().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  out.extend(m.group(1).split())
 return out
positions={r['module']:j for j,r in enumerate(rows)};q=set()
for j,r in enumerate(rows):
 p=D/r['path'];assert p.is_file() and p.stem==r['module'] and sha(p)==r['sha256']
 assert index[p.stem]==[p],(p,index[p.stem])
 imports=header(p);bare=[x for x in imports if '.' not in x];qualified=[x for x in imports if '.' in x]
 assert bare==r['bare_imports'] and qualified==r['qualified_imports']
 for x in bare:assert x in positions and positions[x]<j
 q.update(qualified)
visited=set();todo=[Path(i['root']).stem]
while todo:
 name=todo.pop()
 if name in visited:continue
 visited.add(name);todo.extend(by[name]['bare_imports'])
assert visited==set(by) and rows[-1]['path']==i['root']
assert q=={r['module'] for r in ext} and len(q)==len(ext)
for r in ext:
 p=D/'Lean'/('/'.join(r['module'].split('.'))+'.lean');assert str(p.relative_to(D))==r['path'] and p.is_file() and sha(p)==r['sha256']
for key,added,removed in [('drafts_topological',{'Natural86Endpoint','Natural86Model','P86NaturalCancel','RingNatural86To74'},{'Root74Endpoint'}),('qualified_direct_sources',{'DiophantineConsistency.Compact44.IPRAOrdinary12','DiophantineConsistency.HAExpressionNoZeroEquiv','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAReferenceInductionConversion','DiophantineConsistency.IPRAStandardTheory'},set())]:
 new={r['module'] for r in i[key]};prior={r['module'] for r in old[key]};assert new-prior==added and prior-new==removed
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not run.stderr and run.stdout==(A/'inventory.json').read_bytes()
print(json.dumps({'scope':'initial source-header inventory only; no Lean resolution, transitive qualified imports, object or provider readiness','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'bare_reachable_unique_topological':len(visited),'direct_qualified_unique':len(q),'root74_bare_added':sorted({'Natural86Endpoint','Natural86Model','P86NaturalCancel','RingNatural86To74'}),'root74_bare_removed':['Root74Endpoint'],'root74_qualified_added':5,'author_receipt_replayed':True},sort_keys=True,indent=2))
