#!/usr/bin/env python3
"""Independent source-only snapshot/closure verification; does not invoke Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-slim-overlay'
H=lambda b:hashlib.sha256(b).hexdigest()
pins={A/'README.md':'b7234a05a427c95659c4673e1c8a7f6bb82fec005aedb71b4d0dba5cae4ef806',A/'check_source.py':'6c8b79ea7ff66ab7f9e002f5f997426cf57fe2352a1a2528ecdc053899dde205',A/'inventory.json':'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'}
tail=b"\nIndependent source review: [root74 slim overlay](../../reviews/ordinary14-root74-slim-overlay-independent/README.md).\n"
for p,h in pins.items():
 data=p.read_bytes()
 if p==A/'README.md':
  assert H(data)=='34b9bca6667fe214a34a5a33475c826e5dd69f1dfd4f8df0edfffd9eabf48804'
  assert data.endswith(tail) and H(data[:-len(tail)])==h
 else:assert H(data)==h,(str(p),H(data),h)
raw=json.loads((D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json').read_bytes()); prior=json.loads((D/'research/ordinary14-root78-slim-overlay/inventory.json').read_bytes()); inv=json.loads((A/'inventory.json').read_bytes())
orig={r['module']:r for r in raw['drafts_topological']};old={r['module']:r for r in prior['drafts_topological']};now={r['module']:r for r in inv['drafts_topological']}
assert len(orig)==len(now)==159 and set(orig)==set(now)
actual={p.name[:-9]:p for p in (A/'source').glob('*.lean.src')};assert set(actual)==set(now)
oldimp=b'import DiophantineConsistency.Compact44.C44Short15Facts';newimp=b'import CompactPortBoundsSlim'
oldref=b'C44Short15Facts.port_bounds';newref=b'CompactPortBoundsSlimDraft.port_bounds'
expected={'CompactEquivalence':(1,1),'Compact78To85':(0,1),'Compact78To86':(0,1),'CompactEquivalence8687':(1,1),'CompactEquivalence8788':(1,1),'Quotient88PositiveBridge':(1,1)}
seen_changes={}; bare={}; direct=set()
for name,r in now.items():
 source=(D/orig[name]['path']).read_bytes(); out=actual[name].read_bytes()
 assert H(source)==orig[name]['sha256']==r['source_sha256'] and H(out)==r['overlay_sha256']
 assert out==source.replace(oldimp,newimp).replace(oldref,newref)
 counts=(source.count(oldimp),source.count(oldref))
 if counts!=(0,0):seen_changes[name]=counts
 header=[]
 for line in out.decode().splitlines():
  t=line.strip()
  if not t:continue
  m=re.fullmatch(r'import\s+([\w.]+(?:\s+[\w.]+)*)',t)
  if not m:break
  header.extend(m.group(1).split())
 bare[name]=[x for x in header if '.' not in x]
 assert bare[name]==r['bare_imports'],name
 q=[x for x in header if '.' in x]; assert q==r['qualified_imports'],name
 direct.update(q)
assert seen_changes==expected
assert actual['CompactPortBoundsSlim'].read_bytes()==(D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean').read_bytes()
helper=actual['CompactPortBoundsSlim'].read_text();assert 'namespace DiophantineConsistency.CompactPortBoundsSlimDraft' in helper and 'theorem port_bounds ' in helper
for n in expected:
 assert 'namespace DiophantineConsistency.' in actual[n].read_text()
 def reachable(start,target):
  todo=[start];visited=set()
  while todo:
   x=todo.pop()
   if x==target:return True
   if x in visited:continue
   visited.add(x);todo.extend(bare[x])
  return False
 assert reachable(n,'CompactPortBoundsSlim'),n
order=[r['module'] for r in inv['drafts_topological']];position={n:i for i,n in enumerate(order)}
for n,imports in bare.items():
 for x in imports:assert x in now and position[x]<position[n],(n,x)
visited=set();todo=['Root74Endpoint']
while todo:
 n=todo.pop()
 if n in visited:continue
 visited.add(n);todo.extend(bare[n])
assert visited==set(now) and order[-1]=='Root74Endpoint'
shared=set(old)&set(now); assert len(shared)==138 and set(old)-set(now)=={'Root78Endpoint'}
assert sorted(set(now)-set(old))==inv['new_vs_root78'] and len(inv['new_vs_root78'])==21
for n in shared:assert (D/'research/ordinary14-root78-slim-overlay'/old[n]['path']).read_bytes()==actual[n].read_bytes(),n
assert direct==set(inv['direct_qualified']) and len(direct)==30
assert 'DiophantineConsistency.Compact44.C44Short15Facts' not in direct
for name,row in inv['project_sources'].items():assert H((D/row['path']).read_bytes())==row['sha256'],name
assert len(inv['project_sources'])==1127
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
assert not run.stderr and run.stdout==(A/'inventory.json').read_bytes()
print(json.dumps({'scope':'independent snapshot, bare import reachability/order, direct import and source-hash controls; no Lean/provider proof','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'snapshots':len(now),'changed':seen_changes,'shared_root78':len(shared),'root74_new':len(inv['new_vs_root78']),'direct_qualified':len(direct),'recorded_project_source_hashes_checked':len(inv['project_sources']),'author_receipt_replayed':True},sort_keys=True,indent=2))
