#!/usr/bin/env python3
"""Independent static import graph/receipt review; no Lean invocation."""
import hashlib,json,subprocess,sys
from collections import defaultdict
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-78-85-draft-import-inventory'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
pin(A/'check_source.py','e592961b5e8cbcfd9308532134ff4e3b9dd5ed8ecd15044749fb9a383ae3321e')
receipt=pin(A/'inventory.json','0d6b2e6384810f30c67834a69e6f65d937accb95e3023669be5ceeef9e1bbeac')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-78-85-draft-import-inventory-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='42a1c83732430c26bd062b648d5b680f4f12cae5f179f5d646ae44e51bf82820'
obj=json.loads(receipt);drafts=obj['drafts_topological'];qualified=obj['qualified_direct_sources']
assert obj['root']=='research/ordinary14-78-85-compact-model-composition-draft/Compact78To85.lean'
assert obj['draft_count']==len(drafts)==62 and obj['qualified_direct_count']==len(qualified)==19
assert drafts[-1]['path']==obj['root']
all_stems=defaultdict(list)
for p in (D/'research').rglob('*.lean'):all_stems[p.stem].append(p.relative_to(D).as_posix())
nodes={item['module']:item for item in drafts};assert len(nodes)==len(drafts)
positions={item['module']:i for i,item in enumerate(drafts)}
direct_qualified=set()
for item in drafts:
 p=D/item['path'];assert p.stem==item['module'] and all_stems[p.stem]==[item['path']]
 text=pin(p,item['sha256']).decode();names=[]
 for line in text.splitlines():
  words=line.split()
  if not words:continue
  if words[0]!='import':break
  assert len(words)>1
  names.extend(words[1:])
 bare=[n for n in names if '.' not in n];ext=[n for n in names if '.' in n]
 assert bare==item['bare_imports'] and ext==item['qualified_imports']
 for n in bare:assert n in nodes and positions[n]<positions[item['module']]
 direct_qualified.update(ext)
seen=set();todo=[drafts[-1]['module']]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(nodes[n]['bare_imports'])
assert seen==set(nodes)
assert direct_qualified=={x['module'] for x in qualified}
for item in qualified:
 assert item['path']=='Lean/'+item['module'].replace('.','/')+'.lean'
 pin(D/item['path'],item['sha256'])
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'static direct-header source graph only; no Lean or provider audit',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'drafts':len(drafts),
 'qualified_direct_sources':len(qualified),'reachable_and_topological':True},sort_keys=True,indent=2))
