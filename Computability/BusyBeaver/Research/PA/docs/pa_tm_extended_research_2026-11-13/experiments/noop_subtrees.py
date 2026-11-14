import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from noops import *
from collections import Counter
import time

def subtrees(t):
 out=set()
 def rec(x):
  out.add(x)
  if isnode(x):rec(x[0]);rec(x[1])
 rec(t);return out

def safe(x):
 if not isnode(x):return x not in ['node142','node150',BREAK]
 return safe(x[0])and safe(x[1])

start=time.time();tt=sorted([x for x in subtrees(initial)if safe(x)],key=str)
print('targets',len(tt),flush=True);best=999;bestcases=[];hist=Counter()
for j,targ in enumerate(tt):
 for side in [0,1]:
  t=wrap(initial,targ,side);r,_,sh=build(t);ops=opportunities_fast(r,sh);m=max_matching(ops);c=len(r)//2-len(m);hist[c]+=1
  if c<best:best=c;print('BEST',c,'target',j,'side',side,'raw',len(r)//2,'folds',len(m),flush=True)
  if c<=196:
   bestcases.append({'target':j,'side':side,'cost':c,'grammar':encode(t)})
   if inspect(t,('subtree',j,side)):raise SystemExit()
Path('noop_subtree_results.json').write_text(json.dumps({'targets':len(tt),'histogram':hist,'candidates':bestcases,'seconds':time.time()-start},indent=2))
print('DONE',best,hist,time.time()-start,flush=True)
