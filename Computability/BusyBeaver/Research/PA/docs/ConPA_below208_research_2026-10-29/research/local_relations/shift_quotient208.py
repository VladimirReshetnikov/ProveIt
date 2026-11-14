"""A quotient deleting q with head offset -2d, reversing all q-entry moves.
One-old-step positive-block certificate with exact disjunctive tape guards.
Discovery contexts harvested from source runs are explicitly not certificates.
"""
import sys,json,time,random,hashlib,argparse,itertools,collections
from pathlib import Path
import history_contexts as D
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('--depth',type=int,default=9);p.add_argument('--limit',type=int,default=45);p.add_argument('--output',type=Path,required=True);p.add_argument('--contexts',type=Path);p.add_argument('--mutate',action='store_true');p.add_argument('--cluster',default='all');a=p.parse_args()
t=D.read_table(a.table);states=sorted({q for q,b in t});incoming=collections.defaultdict(list)
for(p,b),(w,d,q)in t.items():incoming[q].append((p,b,w,d))
cluster=set(states if a.cluster=='all' else map(int,a.cluster.split(',')));start=time.monotonic();ctx=({int(q):[tuple(sorted((int(p),b)for p,b in c.items()))for c in cs]for q,cs in json.loads(a.contexts.read_text()).items()}if a.contexts else D.history_contexts(t,a.depth));rng=random.Random(52840)
def project(s,h,drop,keep,offset):return (keep,h+offset)if s==drop else(s,h)
def transition(s,b,drop,keep,bit,act):
 w,d,z=act if s==keep and b==bit else t[s,b]
 return(w,-d,keep)if z==drop else(w,d,z)
samples={}
for q in states:
 samples[q]=[]
 for b in(0,1):
  allowed=[dict(g)for g in ctx[q]if 0 not in dict(g)or dict(g)[0]==b]
  if not allowed:continue
  for i in(0,-1):
   bits={j:rng.randrange(2)for j in range(-a.limit-5,a.limit+6)};bits.update(allowed[i]);bits[0]=b;samples[q].append((bits,b))
def screen(q,initial,b,drop,keep,offset,bit,act):
 ow,od,oz=t[q,b];es,eh=project(oz,od,drop,keep,offset);expected={}if ow==b else{0:ow};delta={};s,h=project(q,0,drop,keep,offset)
 for n in range(a.limit):
  if s==254:return False
  rb=delta.get(h,initial[h]);w,d,z=transition(s,rb,drop,keep,bit,act)
  if w==initial[h]:delta.pop(h,None)
  else:delta[h]=w
  s=z;h+=d
  if s==es and h==eh and delta==expected:return True
 return False

def exact(q,g,drop,keep,offset,bit,act):
 todo=[(dict(g),None,*project(q,0,drop,keep,offset),(),0)];branches=0;durations=[]
 while todo:
  initial,read,s,h,changes,n=todo.pop();branches+=1
  if branches>8192:return None
  if read is None:
   if 0 not in initial:
    for b in(0,1):ni=initial.copy();ni[0]=b;todo.append((ni,b,s,h,changes,n))
    continue
   read=initial[0]
  ow,od,oz=t[q,read];es,eh=project(oz,od,drop,keep,offset);expected=()if ow==read else((0,ow),)
  if n and s==es and h==eh and changes==expected:durations.append(n);continue
  if n>=a.limit or s==254:return None
  if h not in initial:
   for b in(0,1):ni=initial.copy();ni[h]=b;todo.append((ni,read,s,h,changes,n))
   continue
  delta=dict(changes);b=delta.get(h,initial[h]);w,d,z=transition(s,b,drop,keep,bit,act)
  if w==initial[h]:delta.pop(h,None)
  else:delta[h]=w
  todo.append((initial,read,z,h+d,tuple(sorted(delta.items())),n+1))
 return {'branches':branches,'leaves':len(durations),'max_new':max(durations)}
results=[];pairs=trials=survivors=0
for drop in sorted(cluster):
 if drop==0:continue
 ds={d for p,b,w,d in incoming[drop]}
 if len(ds)!=1:continue
 offset=-2*next(iter(ds))
 for keep in states:
  if keep in(0,drop):continue
  pairs+=1
  actions=itertools.product((0,1),(0,1),(-1,1),states)if a.mutate else[(-1,0,1,keep)]
  for bit,w,d,z in actions:
   if z==drop:continue
   trials+=1;act=(w,d,z);qs=(drop,keep)if bit!=-1 else(drop,)
   if not all(screen(q,init,b,drop,keep,offset,bit,act)for q in qs for init,b in samples[q]):continue
   survivors+=1;checks=[]
   for q in qs:
    for g in ctx[q]:
     v=exact(q,g,drop,keep,offset,bit,act)
     if v is None:break
     checks.append(v)
    else:continue
    break
   else:
    record={'drop':drop,'keep':keep,'offset':offset,'mutation':None if bit==-1 else[bit,*act],'checks':checks};results.append(record);print('HIT',record,flush=True)
 if drop%10==0:print('progress',drop,'pairs',pairs,'trials',trials,'survivors',survivors,'seconds',time.monotonic()-start,flush=True)
report={'table':str(a.table),'sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'scope':'All q entries move in one direction; reverse them, merge q into keep with uniform head offset; optional one keeper row mutation. One old step to a positive bounded child block.','depth':a.depth,'limit':a.limit,'contexts':str(a.contexts)if a.contexts else'exact finite history','pairs':pairs,'trials':trials,'finite_survivors':survivors,'results':results,'seconds':time.monotonic()-start};a.output.write_text(json.dumps(report,indent=2)+'\n');print('DONE',len(results),report['seconds'],flush=True)
