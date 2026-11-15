from common import *
from collections import deque,defaultdict
import itertools,time,argparse
ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=3);ap.add_argument('--fuel',type=int,default=31);ap.add_argument('--input');ap.add_argument('--output',type=Path);args=ap.parse_args()
r=args.radius;N=2*r+1;MASK=(1<<N)-1;CENTER=1<<r
old=dict(rows)
if args.input:
 old={}
 for line in Path(args.input).read_text().splitlines():
  q,b,w,d,t=line.split();old[int(q),int(b)]=int(w),d=='R',int(t)
controls=sorted({q for q,b in old});contexts=defaultdict(set);queue=deque([(74,0)]);contexts[74].add(0)
start=time.monotonic()
while queue:
 q,x=queue.popleft();b=(x>>r)&1;w,d,t=old[q,b];x1=(x|CENTER)if w else(x&~CENTER)
 if t==254:continue
 for u in (0,1):
  y=(x1>>1)|(u<<(N-1))if d else((x1<<1)&MASK)|u
  if y not in contexts[t]:contexts[t].add(y);queue.append((t,y))
print('contexts',r,len(contexts),sum(map(len,contexts.values())),time.monotonic()-start,flush=True)
options={};witnesses={}
for iq,q in enumerate(controls):
 for b in (0,1):
  cases=[x for x in contexts[q]if((x>>r)&1)==b]
  if not cases:options[q,b]=None;continue
  opts=None;percase={}
  for x in cases:
   state=q;h=0;mask=x;poss={}
   for k in range(1,args.fuel+1):
    if not -r<=h<=r or state==254:break
    v=(mask>>(r+h))&1;w,d,state=old[state,v]
    flag=1<<(r+h);mask=(mask|flag)if w else(mask&~flag);h+=1 if d else -1
    if abs(h)==1 and ((mask^x)&~CENTER)==0:
     action=((mask>>r)&1,h==1,state)
     if action not in poss:poss[action]=k
   if opts is None:opts=set(poss)
   else:opts&=set(poss)
   percase[x]=poss
   if not opts:raise AssertionError(('originalrowmissing',q,b,x))
  options[q,b]=sorted(opts,key=lambda a:(max(p[a]for p in percase.values()),a))
  for a in opts:witnesses[q,b,a]=[max(p[a]for p in percase.values()),[percase[x][a]for x in cases]]
 if iq%30==0:print('rows',iq,time.monotonic()-start,flush=True)
print('nontrivial',sum(max(0,len(x)-1)if x is not None else 0 for x in options.values()),'unseenrows',[k for k,v in options.items()if v is None],flush=True)
changes=[]
for k,opts in options.items():
 if opts and len(opts)>1:changes.append([*k,old[k],[(a,witnesses[k[0],k[1],a][0])for a in opts if a!=old[k]]])
print('changes',json.dumps(changes),flush=True)
def prunable(excluded):
 keep=set(controls)-set(excluded);chosen={}
 for q in keep:
  for b in (0,1):
   opts=options[q,b]
   if opts is None:chosen[q,b]=(b,True,74);continue
   choices=[a for a in opts if a[2]in keep or a[2]==254]
   if not choices:return None
   chosen[q,b]=choices[0]
 return chosen
found=[]
for q in controls:
 if q==74:continue
 tr=prunable([q])
 if tr is not None:
  todo=[74];reached={74}
  for state in todo:
   for b in (0,1):
    t=tr[state,b][2]
    if t!=254 and t not in reached:reached.add(t);todo.append(t)
  tr={k:a for k,a in tr.items()if k[0]in reached}
  found.append({'removed':q,'states':len(reached),'patch':[[*k,list(a)]for k,a in tr.items()if a!=old[k]]})
  (HERE/f'fresh_accel_r{r}_delete{q}.native.tm').write_text(''.join(f'{q1} {b} {w} {"R"if d else"L"} {t}\n' for(q1,b),(w,d,t)in sorted(tr.items())))
print('FOUND',json.dumps(found),flush=True)
receipt={'radius':r,'fuel':args.fuel,'contexts':sum(map(len,contexts.values())),'per_state_contexts':{q:len(x)for q,x in contexts.items()},'changes':changes,'found':found,'seconds':time.monotonic()-start}
(args.output or HERE/f'fresh_acceleration_r{r}.json').write_text(json.dumps(receipt,indent=2)+'\n')
