#!/usr/bin/env python3
from pathlib import Path
import sys,json
HERE=Path(__file__).resolve().parent
P=HERE.parent/'inputs';sys.path.insert(0,str(P));import compiler as c
c.ROOT=P
n=c.raw_nodes();n.update(node21=('node20','node170'),node171=('node21','node23'),node172=('node7','node171'),node162=('node37','node163'),node164=('node75','node162'));c.raw_nodes=lambda:n
s,ins,cs=c.source(c.read_grammar(P/'pa194.grammar.json'))
by_path={tuple(p):i for i,(p,op,arg) in enumerate(s)}
ls=json.loads((P/'pa194.labels.json').read_text());r={}
for line in (P/'pa194.tm').read_text().splitlines():
 q,b,w,d,z=line.split();r[ls[int(q)],int(b)]=(int(w),d=='R',ls[int(z)])
r.update({(84,0):(0,True,68),(53,0):(0,True,333),(53,1):(1,True,214),(310,0):(0,True,53),(100,0):(0,True,213),(100,1):(1,True,174),(174,0):(0,True,28),(174,1):(1,True,164),(333,0):(0,True,105),(333,1):(1,True,31),(23,0):(0,False,75)})
del r[34,0];del r[34,1]
def frame(q,h,ones):
 if q!=84 or not ones or min(ones)!=h-1:return
 p=()
 while p not in by_path:
  p+=(int(h+len(p)in ones),)
  if len(p)>60:return
 K=len(p)
 while h+K not in ones:
  K+=1
  if h+K>max(ones):return
 want={h-1,h+K};want.update(h+i for i,b in enumerate(p)if b)
 pos=h+K+1;vs=[]
 while pos<=max(ones):
  if pos in ones:return
  pos+=1;start=pos
  while pos in ones:pos+=1
  if pos==start:return
  vs.append(pos-start-1);want.update(range(start,pos))
 if len(vs)>=10 and want==ones:
  return dict(site=by_path[p],path=''.join(map(str,p)),head=h,K=K,registers=[vs[x]for x in c.PHYSICAL],spares=vs[9:])

out=[]
starts=[74,198,66,0,94,40,4,16,64,97,113,75,84]
for start in starts:
 q,h,ones=start,0,set();found=[];last=None
 for step in range(1,200001):
  w,d,q=r[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1
  if q==254:break
  fr=frame(q,h,ones)
  if fr:
   fr['step']=step
   if len(found)<5:found.append(fr)
   last=fr
  if abs(h)>5000 and len(ones)<3:break
 out.append(dict(start=start,steps=step,halted=q==254,final_q=q,final_head=h,ones=len(ones),first_frames=found,last_frame=last))
 print(json.dumps({k:v for k,v in out[-1].items() if k not in ('first_frames','last_frame')}))
(HERE.parent/'receipts/startup_probes.json').write_text(json.dumps(out,indent=2)+'\n')
