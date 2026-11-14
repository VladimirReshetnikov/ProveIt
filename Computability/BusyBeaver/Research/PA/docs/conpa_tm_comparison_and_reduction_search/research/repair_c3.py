from search_folds import *
import sys
sys.path.insert(0,str(BASE/'sources/theory_audit'))
from scan_threshold import frame,run
rows=read_table(BASE/'research/combined.tm')
path=(1,0,1,0,0,1,1);targetpath=(1,0,0,0,0,0)
profiles=[([0]*10+[1]*25,0),([2,4,3,2,1,5,3,6,2,1]+[1]*25,0),([0,0,0,0,0,0,2,0,0]+[1]*26,0),([3,0,2,4,1,0,3,2,4,7]+[1]*25,13)]
hits=[];start=time.time()
for act in itertools.product((0,1),(-1,1),range(196)):
 r=rows.copy();r[18,1]=act;checks=[]
 for vs,gap in profiles:
  _,_,tp=frame(path,vs,gap);_,_,target=frame(targetpath,vs,gap)
  q,h,tape=18,6,tp.copy();ok=False
  for steps in range(1,5001):
   b=int(h in tape)
   if(q,b) not in r:break
   w,d,q=r[q,b]
   if w:tape.add(h)
   else:tape.discard(h)
   h+=d
   if(q,h,tape)==(75,0,target):ok=True;break
   if q==75:break
  if not ok:break
  checks.append(steps)
 else:
  hit={'action':act,'steps':checks};hits.append(hit);print('HIT',hit,flush=True)
(BASE/'research/c3_repairs.json').write_text(json.dumps(hits,indent=2))
print('DONE',len(hits),time.time()-start,flush=True)
