import symbolic_core as c
import json,time
from pathlib import Path
T,labels=c.machine();items=json.loads((Path(__file__).resolve().parent/'register_entry_analysis.json').read_text())

# Assign physical slots to the nine logical register roles.
def changed(perm):
 out=T.copy()
 for x in items:
  q,b=x['edge'];r=x['calls'][0][1];w,d,n=out[q,b];out[q,b]=(w,d,c.SK[perm[r]])
 return out

def clean(q,h,tape,perm):
 if q!=84 or h not in tape or h-1 not in tape or any(x<h-1 for x in tape):return None
 right=sorted(x-h for x in tape if x>h)
 if not right:return None
 gap=right[0]
 if gap<48:return None
 last=right[-1];i=gap+1;vs=[]
 while i<=last:
  if h+i in tape:return None
  i+=1;j=i
  while h+i in tape:i+=1
  if i==j:return None
  vs.append(i-j-1)
 expected=[0]*9;expected[perm[0]]=2
 if len(vs)>=10 and vs[:9]==expected:return {'head':h,'gap':gap,'registers':vs}
 return None

def startup(rows,perm,limit=1000000):
 q=74;h=0;tape=set();maxwidth=0
 for n in range(limit):
  result=clean(q,h,tape,perm)
  if result:return dict(steps=n,**result)
  if q==254:return {'halted':True,'steps':n}
  b=int(h in tape);w,d,q=rows[q,b]
  if w:tape.add(h)
  else:tape.discard(h)
  h+=1 if d else-1
 return {'limited':limit,'state':q,'ones':len(tape)}

if __name__=='__main__':
 base=c.PHYSICAL.copy();perm=base.copy();perm[4],perm[5]=perm[5],perm[4]
 rows=changed(perm);c.PHYSICAL[:]=perm
 print('permutation',perm,flush=True)
 print('runtime',c.validate(rows,c.contracts()),flush=True)
 print('startup',startup(rows,perm),flush=True)
