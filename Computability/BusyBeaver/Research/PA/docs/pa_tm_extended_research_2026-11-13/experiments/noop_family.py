import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from noops import *
from collections import Counter
import time

NODES=raw_nodes();ROWS,_=machine();PATHS={}
def paths(n,p):
 if not isinstance(n,str):return
 PATHS.setdefault(n,p)
 for b,c in enumerate(NODES[n]):paths(c,p+[b])
paths('node172',[])

def native_state(n):
 p=PATHS[n];q=84;h=0;bits={-1:1,**dict(enumerate(p))}
 for k in range(1000):
  if h==len(p):return q
  b=bits.get(h,0);w,d,q=ROWS[q,b];bits[h]=w;h+=1 if d else -1
 raise ValueError(n)
NOOPS={n:native_state(n)for n,s in NODES.items()if s[0]in[('leaf','dec',6),('leaf','dec',7)]}
MACROS.update(NOOPS)

def subtrees(t):
 out=set()
 def rec(x):
  out.add(x)
  if isnode(x):rec(x[0]);rec(x[1])
 rec(t);return out

def safe(x):
 if not isnode(x):return x not in ['node142','node150',BREAK]
 return safe(x[0])and safe(x[1])

def insert(t,target,side,noop):
 if t==target:return(noop,t)if side==0 else(t,noop)
 if isnode(t):return insert(t[0],target,side,noop),insert(t[1],target,side,noop)
 return t

start=time.time();targets=sorted([x for x in subtrees(initial)if safe(x)],key=str);best=999;hist=Counter();selected=[]
print('nops',NOOPS,'targets',len(targets),flush=True)
for ni,(nop,state)in enumerate(NOOPS.items()):
 for j,targ in enumerate(targets):
  for side in[0,1]:
   t=insert(initial,targ,side,nop);r,_,sh=build(t);ops=opportunities_fast(r,sh);m=max_matching(ops);c=len(r)//2-len(m);hist[c]+=1
   if c<best:best=c;print('BEST',c,nop,j,side,'raw',len(r)//2,'folds',len(m),flush=True)
   if c<=196:
    selected.append({'nop':nop,'target':j,'side':side,'cost':c,'grammar':encode(t),'folds':m})
    Path('noop_family_candidates.json').write_text(json.dumps(selected,indent=2))
 print('progress',ni,'best',best,'selected',len(selected),'seconds',time.time()-start,flush=True)
Path('noop_family_result.json').write_text(json.dumps({'nops':NOOPS,'targets':len(targets),'histogram':hist,'selected':selected,'seconds':time.time()-start},indent=2))
print('DONE',best,hist,time.time()-start,flush=True)
