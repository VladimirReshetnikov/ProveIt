from pathlib import Path
import ast, hashlib, json, os, re
from collections import deque
H=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-bfs-field-cast-bridge-prototype');D=H.parents[1];src=(H/'run.py').read_text();tree=ast.parse(src)
ns={'Path':Path,'H':H,'D':D,'SRC':H/'Trace75BFSFieldCastBridge.lean'}
for n in tree.body:
 if isinstance(n,ast.Assign):
  name=n.targets[0]
  if isinstance(name,ast.Name) and (name.id in {'ATT','RESULT','INITIAL','OUTER','BFSATT','BFS','OUTSIDE','HELPER','LEAN','PACK','CORE','PINS','CLIENTS'} or name.id.endswith('ROOT')):
   exec(compile(ast.Module(body=[n],type_ignores=[]),'runner-assign','exec'),ns)
  elif isinstance(name,ast.Subscript) and isinstance(name.value,ast.Name) and name.value.id=='PINS':
   exec(compile(ast.Module(body=[n],type_ignores=[]),'runner-pin','exec'),ns)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def insist(b,msg):
 if not b:raise RuntimeError(msg)
for p,h in ns['PINS'].items():insist(sha(p)==h,'pin '+str(p))
run=json.loads(ns['RESULT'].read_text()); initial=json.loads(ns['INITIAL'].read_text());outside=json.loads(ns['OUTSIDE'].read_text());bfs=json.loads(ns['BFS'].read_text());expected=dict(initial)
for st in run['stages']:
 insist(st['status']=='PASS' and st['exit']==0 and st['reason'] is None and st['module'] not in expected,'stage');expected[st['module']]=st['object']
insist(len(expected)==1977 and len(outside)==80,'counts');lib=Path(run['output_root'])/'lib'
S=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def stem(n):return n.replace('.','/')
def check_bundle(path,record):
 for suffix in S:
  p=Path(str(path)+suffix);old=record[suffix]
  insist(os.path.lexists(p)==(old is not None),'presence '+str(p))
  if old is not None:insist(p.is_file() and sha(p)==old['sha256'] and str(p.resolve(strict=True))==old['resolved'],'bytes/target '+str(p))
for n,r in expected.items():check_bundle(lib/stem(n),r)
actual={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()};wanted={stem(n)+s for n,r in expected.items() for s,x in r.items() if x is not None};insist(actual==wanted,'union names')
clients=ns['CLIENTS'];insist(len(clients)==15 and len({n for _,n,_,_ in clients})==15,'clients count')
roots=[row[0] for row in clients];insist(len(set(roots))==15,'client roots unique')
for root,n,sh,oh in clients:
 insist(root.is_dir() and not root.is_symlink() and root.resolve()==root.absolute(),'root')
 for ext,h in (('.lean',sh),('.olean',oh)):
  p=root/(n+ext);insist(p.is_file() and not p.is_symlink() and p.resolve()==p.absolute() and sha(p)==h,'client '+str(p))
 insist({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}=={n+'.lean',n+'.olean'},'client files')
 hits=[]
 for p in (D/'research').glob('*/observations/attempt01/result.json'):
  try:r=json.loads(p.read_text())
  except Exception:continue
  if r.get('output_root')==str(root) and r.get('object_sha256')==oh:hits.append((p,r))
 insist(len(hits)==1,'producer '+n+' '+str(len(hits)))
 producer=hits[0][1];insist(producer['status']=='PASS' and producer['stage']['exit']==0 and producer['header']['exit']==0,'producer status '+n)
 for earlier in roots[:roots.index(root)]:insist(not os.path.lexists(earlier/(n+'.olean')),'client shadow '+n)
roots+= [lib,ns['PACK'],ns['CORE']]
for n,r in outside.items():
 rel=stem(n)+'.olean';matches=[root/rel for root in roots if os.path.lexists(root/rel)];insist(matches and matches[0].is_file() and str(matches[0])==r['.olean']['path'],'outside first '+n);check_bundle(Path(str(matches[0])[:-6]),r)
for n in expected:
 for client in roots[:15]:insist(not os.path.lexists(client/(stem(n)+'.olean')),'project shadow '+n)
for n in ['DiophantineConsistency.CompactFieldCastBridge']:
 seen=set();boundary=set();queue=deque([n]);project=bfs['closure']['project'];ext=bfs['closure']['outside']
 while queue:
  x=queue.popleft()
  if x in seen or x in boundary:continue
  if x not in project:boundary.add(x);continue
  seen.add(x);queue.extend(project[x]['imports'])
 insist(boundary<=ext.keys(),'outside boundary')
 for x in seen:
  for suf in S:
   a=expected[x][suf];b=project[x]['companions'][suf];insist((a is None)==(b is None) and (a is None or a['sha256']==b['sha256']),'subtree '+x+suf)
 for x in boundary:
  for suf in S:
   a=outside[x][suf];b=ext[x]['companions'][suf];insist((a is None)==(b is None) and (a is None or a['sha256']==b['sha256']),'subtree outside '+x+suf)
 print(n,len(seen),'project',len(boundary),'outside')
print('PASS',len(ns['PINS']),'pinned inputs',len(clients),'client roots',len(expected),'project',len(outside),'outside')
