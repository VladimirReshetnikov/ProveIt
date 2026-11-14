from pathlib import Path
import json,time,sys
H=Path(__file__).resolve().parent
T={}
for l in(H/'B8_parity_folded.tm').read_text().splitlines():
 q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
source=json.loads((H/'B8_source_sites.json').read_text());leafs={tuple(p):i for i,(p,op)in enumerate(source)};maximum=max(map(len,leafs));physical=[6,2,0,4,3,7,8,5,1]
seed=leafs[(1,0,0,0,0,0)]
def frame(ones,head):
 if head-1 not in ones or any(x<head-1 for x in ones):return None
 p=();k=0
 while p not in leafs:
  p=p+(int(head+k in ones),);k+=1
  if k>maximum:return None
 rest=[x-head for x in ones if x>=head+k]
 if not rest:return None
 gap=min(rest)
 if gap<maximum+2:return None
 # A unary file is zero delimiter + at least one1 per register, after header1.
 x=head+gap+1;values=[]
 while x+1 in ones:
  if x in ones:return None
  y=x+1
  while y in ones:y+=1
  values.append(y-x-2);x=y
 if len(values)<10 or any(y>x for y in ones):return None
 return dict(site=leafs[p],path=''.join(map(str,p)),gap=gap,registers=[values[physical[i]]for i in range(9)],spares=values[9:])
ones=set();q=0;head=0;start=time.time();roots=0;count=0;first=[];seedvisits=[];bound=int(sys.argv[1])if len(sys.argv)>1 else 10_000_000;halt=None
for i in range(bound+1):
 if q==75:
  roots+=1;f=frame(ones,head)
  if f is not None:
   count+=1
   if len(first)<20:first.append(dict(step=i,head=head,**f))
   if f['site']==seed and len(seedvisits)<30:
    seedvisits.append(dict(step=i,head=head,**f))
   if f['site']==seed and f['registers'][0]>=2 and f['registers'][1:]==[0]*8:
    print('REACHED_PERMITTED_SEED',i,head,f,flush=True);break
 if (q,int(head in ones))not in T:halt=dict(step=i,state=q,head=head);break
 w,d,q=T[q,int(head in ones)]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=d
else:i=bound
out=dict(bound=bound,steps=i,halt=halt,root_visits=roots,clean_frames=count,minimum_gap=maximum+2,required_runtime_gap=48,first_clean_frames=first,seed_visits=seedvisits,final_state=q,final_head=head,final_ones=len(ones),seconds=time.time()-start,scope='Bounded complete-tape startup inspection. A cleanframe is syntactic, and gap<48 needs a revised uniform runtime argument. No nonhalting or failure-of-initialization inference.')
(H/'B8_clean_frames_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k not in('first_clean_frames','seed_visits')},flush=True);print('FIRST',first[:3],flush=True);print('SEEDS',seedvisits[:3],flush=True)
