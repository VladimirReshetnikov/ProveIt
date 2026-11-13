#!/usr/bin/env python3
from pathlib import Path
from collections import defaultdict
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-endpoint-import-inventory'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'0e5b27d905ef523ab80fada3dae904cafb7d0d720f1c2f05088019fc1c0a9e23',A/'check_source.py':'65b5b3be8e767dd19c185022828d975465c6db4b2a8f16d8d587b2099055bc90',A/'inventory.json':'2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7'}
tail=b'\nIndependent source review: [root74 endpoint import inventory](../../reviews/ordinary14-root74-endpoint-import-inventory-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='8bc71bb6acbf52ff9ea618d6258b7218987e1852cb27850c7ac807e093ec9b1e'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
j=json.loads((A/'inventory.json').read_bytes());rows=j['drafts_topological'];qual=j['qualified_direct_sources'];assert len(rows)==j['draft_count']==159 and len(qual)==j['qualified_direct_count']==31
index=defaultdict(list)
for p in (D/'research').rglob('*.lean'):index[p.stem].append(p)
modules={x['module']:x for x in rows};assert len(modules)==len(rows)
positions={row['module']:n for n,row in enumerate(rows)}
qualified=set();edges=0
for row in rows:
 n=row['module'];p=D/row['path'];assert index[n]==[p] and p.is_file() and sha(p)==row['sha256'],n
 imports=[]
 for line in p.read_text().splitlines():
  words=line.split()
  if not words:continue
  if words[0]!='import':break
  assert len(words)>1 and all(all(c.isalnum() or c in '_.' for c in w) for w in words[1:]),(n,line)
  imports.extend(words[1:])
 bare=[x for x in imports if '.' not in x];q=[x for x in imports if '.' in x]
 assert bare==row['bare_imports'] and q==row['qualified_imports'],n
 for x in bare:assert x in positions and positions[x]<positions[n],(n,x)
 qualified.update(q);edges+=len(bare)
# Traverse recorded edges independently; all listed modules must be reachable.
root=Path(j['root']).stem;assert root=='Root74Endpoint' and rows[-1]['module']==root
reachable=set();todo=[root]
while todo:
 n=todo.pop()
 if n in reachable:continue
 reachable.add(n);todo.extend(modules[n]['bare_imports'])
assert reachable==set(modules)
qrows={x['module']:x for x in qual};assert len(qrows)==len(qual) and qualified==set(qrows)
for n,row in qrows.items():
 p=D/'Lean'/('/'.join(n.split('.'))+'.lean')
 assert p.is_file() and str(p.relative_to(D))==row['path'] and sha(p)==row['sha256'],n
heavy='DiophantineConsistency.Compact44.C44Short15Facts';assert heavy in qrows
heavy_importers=sorted(r['module'] for r in rows if heavy in r['qualified_imports'])
assert heavy_importers and all(name in reachable for name in heavy_importers)
assert {'Root74PositiveBridge','Root78PositiveBridge','CompactPortBoundsSlim','Root74Endpoint'}<=reachable
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'inventory.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'independent initial-header source inventory review; no Lean, transitive qualified source or provider proof','reachable_bare_modules':len(reachable),'bare_edges':edges,'direct_qualified_sources':len(qualified),'heavy_direct_importers':heavy_importers,'author_inventory_replayed':True,'reviewed_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
