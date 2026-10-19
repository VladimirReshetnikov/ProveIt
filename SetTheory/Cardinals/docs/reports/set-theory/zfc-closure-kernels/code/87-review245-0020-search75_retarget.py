"""Self-authored symbolic row search for deleting state255 while preserving both contexts."""
from pathlib import Path
import os
if not __debug__: raise RuntimeError("Assertions must remain enabled")
import json
P=Path(os.environ.get('B245_OUTPUT',Path(__file__).resolve().parent.parent/'results'));t={}
for l in(P/'candidates/candidate_appendzero244_old.tm').read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,n=l.split();t[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(n))
states=sorted({q for q,b in t})
def prove(row,eof,spare=1,limit=20):
 w,d,q=row;initial={-2:1,-1:0,0:0,1:0 if eof else 1};cells={0:w};count=0;worst=0
 pending=[(q,d,initial,cells,0)]
 def ini_at(ini,x):return ini.get(x,0 if eof and x>=0 else None)
 while pending:
  q,h,ini,cells,step=pending.pop();count+=1
  if count>20000:return False,'BRANCH_LIMIT'
  desired={0:1}
  if eof:desired.update({x:1 for x in range(1,spare+1)})
  if q==131 and h==(-1 if eof else 0):
   good=True
   for x in set(cells)|set(desired):
    target=desired.get(x,ini_at(ini,x));actual=cells.get(x,ini_at(ini,x))
    if actual is None or actual!=target:good=False;break
   if good:worst=max(worst,step);continue
  if step>=limit:return False,'STEP_LIMIT'
  if(q,0)not in t:return False,'HALT'
  val=cells.get(h,ini_at(ini,h))
  if val is None:
   for v in[0,1]:
    new=ini.copy();new[h]=v;pending.append((q,h,new,cells,step))
   continue
  write,d,n=t[q,val];newcells=cells.copy();newcells[h]=write
  pending.append((n,h+d,ini,newcells,step+1))
 return True,worst
cdhits=[];hits=[]
for q in states:
 for w in[0,1]:
  for d in[-1,1]:
   row=(w,d,q);r=prove(row,False)
   if r[0]:
    cdhits.append({'row':row,'maxsteps':r[1]})
    for spare in range(4):
     z=prove(row,True,spare)
     if z[0]:hits.append({'row':row,'spare':spare,'maxsteps_cd':r[1],'maxsteps_eof':z[1]})
res={'tested_rows':len(states)*4,'maxsteps':20,'cdhits':cdhits,'hits':hits};(P/'retarget75_results.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
