#!/usr/bin/env python3
"""Sound finite product invariant for the source register machine.

Classes are singleton values below the requested threshold, then two parity
classes. Source/calibration and graph_interface.py are inherited from ProveIt
archive3 in commit ec480205a17f9e2b5f575b4c5d9c2279ace903f7.
The new invariant and replacement theorem do not claim a smaller binary TM.
"""
import importlib.util,json,hashlib,sys,argparse
from pathlib import Path
from collections import deque,Counter
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--threshold',type=int,default=16)
ap.add_argument('--source',type=Path,default=root/'source.json')
ap.add_argument('--output',type=Path,default=root/'replay')
args=ap.parse_args()
assert __debug__ and args.threshold>=1,'Assertions must remain enabled; threshold must be positive.'
source=args.source.resolve()
assert hashlib.sha256(source.read_bytes()).hexdigest()=='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6','Source bytes changed.'
args.output.mkdir(parents=True,exist_ok=True)
helper=root/'graph_interface.py'
spec=importlib.util.spec_from_file_location('source_graph',helper);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ordered,g,start,depth=m.graph(json.loads(source.read_text()))
# Classes are exact values below K, then parity classes at or above K.
K=args.threshold
classes=tuple(1<<i for i in range(K+2))
def box(v):return 1<<(v if v<K else K+(v%2))
def shift(a,d):
 r=0
 while a:
  bit=a&-a;i=bit.bit_length()-1;a-=bit
  if i<K:
   if i+d>=0:r|=box(i+d)
  else:
   first=K+((i-K-K)%2)
   r|=box(first+d)|box(first+2+d)
 return r
def incmask(a):return shift(a,1)
def decmask(a):return shift(a,-1)
facts=[None]*len(g);facts[start]=tuple(box(x) for x in (3,0,0,0,3,0,0,0,0));todo=deque([start]);in_todo={start};updates=0
while todo:
 i=todo.popleft();in_todo.remove(i);a=facts[i];d=g[i];successors=[]
 if d[0]=='INC':
  n=list(a);n[d[1]]=incmask(n[d[1]]);successors.append((d[2],n))
 elif d[0]=='DEC':
  if a[d[1]]&~1:
   n=list(a);n[d[1]]=decmask(n[d[1]]&~1);successors.append((d[2],n))
  if a[d[1]]&1:
   n=list(a);n[d[1]]=1;successors.append((d[3],n))
 elif d[0]=='JUMP':successors.append((d[1],list(a)))
 else:assert d==('HALT',)
 for j,n in successors:
  old=facts[j];new=tuple(n) if old is None else tuple(x|y for x,y in zip(old,n))
  if new!=old:
   facts[j]=new;updates+=1
   if j not in in_todo:todo.append(j);in_todo.add(j)

# Independent post-fixpoint scan: transfer images included, seed included.
assert all(box(x)&~a==0 for x,a in zip((3,0,0,0,3,0,0,0,0),facts[start]))
assert all(a is None or all(0<v<(1<<(K+2)) for v in a) for a in facts)
for i,a in enumerate(facts):
 if a is None:continue
 d=g[i]
 for guard in ((0,1) if d[0]=='DEC' else (0,)):
  b=list(a)
  if d[0]=='INC':b[d[1]]=incmask(b[d[1]]);j=d[2]
  elif d[0]=='DEC':
   if guard==0:
    if not a[d[1]]&1:continue
    b[d[1]]=1;j=d[3]
   else:
    if not a[d[1]]&~1:continue
    b[d[1]]=decmask(b[d[1]]&~1);j=d[2]
  elif d[0]=='JUMP':j=d[1]
  else:continue
  assert facts[j] is not None and all(x&~y==0 for x,y in zip(b,facts[j]))
missing=[i for i,a in enumerate(facts) if a is None]
forced=[]
for i,a in enumerate(facts):
 if a is not None and g[i][0]=='DEC':
  value=a[g[i][1]]
  if value==1:forced.append({'index':i,'path':ordered[i][0],'reg':g[i][1],'only':'zero'})
  elif not value&1:forced.append({'index':i,'path':ordered[i][0],'reg':g[i][1],'only':'positive'})
summary={'status':'PASS_FINITE_PRODUCT_INVARIANT','domain':list(range(K))+['large even','large odd'],'initial_registers':[3,0,0,0,3,0,0,0,0],'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'instructions':len(g),'reachable_in_abstraction':sum(a is not None for a in facts),'unreachable_instructions':missing,'forced_decrement_guards':forced,'updates':updates,'scope':'Sound ordinary forward invariant for source-level register values; no binary-state reduction follows by itself.'}
(args.output/f'source_abstract_summary_k{K}.json').write_text(json.dumps(summary,indent=2)+'\n')
(args.output/f'source_abstract_facts_k{K}.json').write_text(json.dumps(facts)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ('unreachable_instructions','forced_decrement_guards')},indent=2));print('unreachable',len(missing),'forced_guards',len(forced));print('forced_first',forced[:20])
