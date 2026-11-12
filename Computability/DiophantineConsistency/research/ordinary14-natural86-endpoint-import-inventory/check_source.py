#!/usr/bin/env python3
"""Static direct source-import inventory only; never invokes Lean."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
root=D/'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean'
by=defaultdict(list)
for p in (D/'research').rglob('*.lean'):by[p.stem].append(p)
graph={};external={};seen=set();todo=[root]
while todo:
 p=todo.pop()
 if p in seen:continue
 seen.add(p);bare=[];qualified=[]
 for line in p.read_text().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  for name in m.group(1).split():
   if '.' in name:
    target=D/'Lean'/('/'.join(name.split('.'))+'.lean')
    assert target.is_file(),(str(p),name)
    qualified.append(name);external[name]=target
   else:
    opts=by[name];assert len(opts)==1,(str(p),name,[str(x) for x in opts])
    bare.append(name);todo.append(opts[0])
 graph[p]={'bare_imports':bare,'qualified_imports':qualified}
order=[];vis=set();active=set()
def visit(p):
 if p in vis:return
 assert p not in active,('cycle',str(p));active.add(p)
 for name in graph[p]['bare_imports']:visit(by[name][0])
 active.remove(p);vis.add(p);order.append(p)
visit(root)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(D))
print(json.dumps({'scope':'static initial import headers in draft closure only; no Lean, object route, transitive qualified-source closure or provider audit','root':rel(root),'draft_count':len(order),'qualified_direct_count':len(external),'drafts_topological':[{'module':p.stem,'path':rel(p),'sha256':sha(p),**graph[p]} for p in order],'qualified_direct_sources':[{'module':n,'path':rel(p),'sha256':sha(p)} for n,p in sorted(external.items())]},sort_keys=True,indent=2))
