"""Self-authored bounded symbolic routing equivalence search. Repository files are data only."""
from pathlib import Path
import os
if not __debug__: raise RuntimeError("Assertions must remain enabled")
import json
ROOT=Path(os.environ.get('B245_OUTPUT',Path(__file__).resolve().parent.parent/'results'))
def parse(p):
 t={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,n=l.split();t[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(n))
 return t
t=parse(ROOT/'candidates/candidate_reassociation244_old.tm')
states=sorted({q for q,b in t})
# Want old route218/0's two-case exact postcondition.
def prove(q,h,w,b,limit):
 initial={-1:b,0:0}; cells={0:w}; count=0; worst=0
 pending=[(q,h,initial,cells,0)]
 while pending:
  q,h,ini,cells,step=pending.pop();count+=1
  if count>10000:return False,'BRANCH_LIMIT'
  if q==(23 if b==0 else 105)and h==1 and all(v==ini.get(x)for x,v in cells.items()):
   worst=max(worst,step);continue
  if step>=limit:return False,'STEP_LIMIT'
  if(q,0)not in t:return False,'HALT'
  val=cells.get(h,ini.get(h))
  if val is None:
   for v in[0,1]:
    new=ini.copy();new[h]=v;pending.append((q,h,new,cells,step))
   continue
  write,d,n=t[q,val]
  newcells=cells.copy();newcells[h]=write
  pending.append((n,h+d,ini,newcells,step+1))
 return True,worst
hits=[]
for q in states:
 for w in[0,1]:
  for d in[-1,1]:
   good=[prove(q,d,w,b,12)for b in[0,1]]
   if all(x[0]for x in good):hits.append({'row':[w,'R'if d==1 else 'L',q],'tail_max_steps':[x[1]for x in good]})
print(json.dumps({'tested_rows':len(states)*4,'max_steps_after_row':12,'hits':hits},indent=2))
(ROOT/'retarget218_results.json').write_text(json.dumps({'tested_rows':len(states)*4,'max_steps_after_row':12,'hits':hits},indent=2)+'\n')
