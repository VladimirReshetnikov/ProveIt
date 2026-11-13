#!/usr/bin/env python3
"""Source-declared BFS paths, not compiled object import ancestry."""
import collections,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];ROOT=HERE.parents[3]
P=TASK/'research/current14-printed-port-extension-plan';BASE=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json')
FOUNDATION=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation');MATH=Path('/home/codex/src/Proofs/.lake/packages/mathlib')
rows=json.loads(BASE.read_text())['sources'].copy()
for fn in ('kernel-manifest.json','masks-manifest.json'):
 for n,r in json.loads((P/fn).read_text())['sources'].items():
  if n in rows and (rows[n]['sha256']!=r['sha256'] or rows[n]['imports']!=r['imports']):raise ValueError(('source conflict',n))
  rows[n]=r

def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   while i<len(s) and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 if depth:raise ValueError('unclosed comment')
 return ''.join(out)
cache={};skipped={}
def node(n):
 if n in cache:return cache[n]
 if n in rows:p=ROOT/rows[n]['workspace_path']
 elif n.startswith('Foundation.'):p=FOUNDATION/(n.replace('.','/')+'.lean')
 elif n.startswith('Mathlib.'):p=MATH/(n.replace('.','/')+'.lean')
 else:return None
 if not p.is_file():return None
 raw=p.read_bytes();sha=hashlib.sha256(raw).hexdigest()
 if n in rows and sha!=rows[n]['sha256']:raise ValueError(('project source drift',n))
 deps=[]
 try:text=uncomment(raw.decode())
 except ValueError as exc:
  skipped[n]=str(exc);return None
 for line in text.splitlines():
  m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',line)
  if m:
   names=m.group(1).split()
   if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",x) for x in names):raise ValueError(('unsupported import',n,line))
   deps.extend(names)
 cache[n]={'source':str(p),'sha256':sha,'imports':deps};return cache[n]

def find(starts,target):
 queue=collections.deque(starts);parent={x:None for x in starts}
 while queue:
  n=queue.popleft()
  if n==target:
   seq=[]
   while n is not None:seq.append(n);n=parent[n]
   return list(reversed(seq))
  item=node(n)
  if item is None:continue
  for d in item['imports']:
   if d not in parent:parent[d]=n;queue.append(d)
 return None
starts=['DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011']
target='Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber'
queue=collections.deque(starts);seen=set();reverse=collections.defaultdict(set)
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n);item=node(n)
 if item is None:continue
 for d in item['imports']:
  if d=='Mathlib.Tactic':continue
  reverse[d].add(n)
  if d not in seen:queue.append(d)
ancestors=set();queue=collections.deque([target])
while queue:
 n=queue.popleft()
 if n in ancestors:continue
 ancestors.add(n);queue.extend(reverse[n]-ancestors)
boundary=[]
for project in sorted(seen & set(rows)):
 for dep in node(project)['imports']:
  if dep!='Mathlib.Tactic' and dep not in rows and dep in ancestors:
   boundary.append({'project':project,'external':dep})
result={'status':'SOURCE_GRAPH_ONLY','excluded_edge_target':'Mathlib.Tactic','target':target,
        'reachable_source_modules':len(cache),'skipped_sources':skipped,'boundary_edges':boundary,
        'scope':'Source-header graph only; omitted unsupported nodes and not compiled transitive object evidence.'}
output=HERE/'source-boundary-without-tactic.json'
with output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({'count':len(boundary),'boundary_edges':boundary,'skipped':len(skipped)},indent=2))
