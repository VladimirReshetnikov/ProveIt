from pathlib import Path
from collections import defaultdict,Counter
import json
BASE=Path(__file__).resolve().parent.parent/'baseline/rotation240'
sites=json.loads((BASE/'sites_logical.json').read_text())
rows={}
for line in (BASE/'zfc_rotation240_old.tm').read_text().splitlines():
 if line.startswith('#'):continue
 q,b,w,d,t=line.split();rows[int(q),int(b)]=int(w),d,int(t)
leaf={p:(op,r) for p,op,r in sites}
prefixes=set()
for p in leaf:
 for i in range(len(p)):prefixes.add(p[:i])
ids={}; structures=[]; pathnode={};occ=defaultdict(list)
def intern(p):
 key=leaf[p] if p in leaf else (intern(p+'0'),intern(p+'1'))
 if key not in ids:ids[key]=len(ids);structures.append(key)
 n=ids[key];pathnode[p]=n;occ[n].append(p);return n
root=intern('')
def leaves(n):
 x=structures[n]
 return [x] if isinstance(x[0],str) else leaves(x[0])+leaves(x[1])
def shape(n):
 x=structures[n]
 return ':'.join(map(str,x)) if isinstance(x[0],str) else '('+shape(x[0])+','+shape(x[1])+')'
qpaths=defaultdict(list);problem=[]
for p in sorted(prefixes):
 q=96
 for b in p:
  w,d,q2=rows[q,int(b)]
  if w!=int(b) or d!='R':break
  q=q2
 else:qpaths[q].append(p);continue
 problem.append(p)
qnodes={q:set(pathnode[p] for p in ps) for q,ps in qpaths.items()}
print('unique',len(structures),'interior',len(structures)-len(set(leaf.values())), 'prefixes',len(prefixes),'qpath',len(qpaths),'problempath',len(problem))
for q,ns in sorted(qnodes.items()):
 if len(ns)>1:print('INCONSISTENT',q,len(ns))
for n,x in enumerate(structures):
 if isinstance(x[0],str) or len(leaves(n))>40:continue
 qq=[q for q,ns in qnodes.items() if ns=={n}]
 print(n,qq,len(occ[n]),len(leaves(n)),shape(n))
(Path(__file__).parent/'mapping.json').write_text(json.dumps({'structures':structures,'pathnode':pathnode,'qnodes':{q:list(ns) for q,ns in qnodes.items()},'qpaths':dict(qpaths),'problem':problem},indent=2))
