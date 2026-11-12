#!/usr/bin/env python3
"""Independent static draft-header import inventory review; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
from collections import defaultdict
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-root78-endpoint-import-inventory'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
pin(A/'check_source.py','cec2fb0a58b1e248085dc694759070629cd6f4d52c9c401b9aed0ec6393133eb')
receipt=pin(A/'inventory.json','7ad6df78af30ef073da84dc14d5507537f3821d08e8716b8c368d4ef3cbdc848')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-root78-endpoint-import-inventory-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='a4ec5bca2f8419b66b9720a27ca161866a7c884076180ae3e7dde025188e2c5b'
data=json.loads(receipt);records=data['drafts_topological'];assert len(records)==138==data['draft_count']
assert len(data['qualified_direct_sources'])==25==data['qualified_direct_count']
index={x['module']:i for i,x in enumerate(records)};assert len(index)==len(records)
lookup=defaultdict(list)
for p in (D/'research').rglob('*.lean'):lookup[p.stem].append(p)
external={};edges={}
for i,rec in enumerate(records):
 p=D/rec['path'];assert p.stem==rec['module'] and sha(p.read_bytes())==rec['sha256']
 bare=[];qualified=[]
 for line in p.read_text().splitlines():
  t=line.strip()
  if not t:continue
  if not re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',t):break
  for name in t.split()[1:]:
   if '.' in name:qualified.append(name);external[name]=D/'Lean'/('/'.join(name.split('.'))+'.lean')
   else:
    bare.append(name);assert len(lookup[name])==1 and index[name]<i
 assert bare==rec['bare_imports'] and qualified==rec['qualified_imports']
 edges[rec['module']]=bare
root=Path(data['root']).stem;seen=set();todo=[root]
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);todo.extend(edges[m])
assert seen==set(index)
actual={e['module']:(e['path'],e['sha256']) for e in data['qualified_direct_sources']}
assert set(actual)==set(external)
for name,p in external.items():
 assert p.is_file() and actual[name]==(str(p.relative_to(D)),sha(p.read_bytes()))
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'static initial-header source inventory review only; no Lean or provider audit',
 'draft_count':len(records),'qualified_direct_count':len(external)},sort_keys=True,indent=2))
