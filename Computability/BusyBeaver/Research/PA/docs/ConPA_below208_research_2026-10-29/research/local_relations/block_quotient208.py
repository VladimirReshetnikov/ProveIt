import sys,json,time,random,hashlib,argparse,itertools,collections
from pathlib import Path
import history_contexts as D
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('--depth',type=int,default=9);p.add_argument('--limit',type=int,default=31);p.add_argument('--output',type=Path,required=True);p.add_argument('--contexts',type=Path);p.add_argument('--cluster',default='163,211,217,215,157,184,67,148,186');a=p.parse_args()
t=D.read_table(a.table);states=sorted({q for q,b in t});cluster=set(states if a.cluster=='all' else map(int,a.cluster.split(',')));start=time.monotonic()
ctx=({int(q):[tuple(sorted((int(p),b) for p,b in c.items())) for c in cs] for q,cs in json.loads(a.contexts.read_text()).items()} if a.contexts else D.history_contexts(t,a.depth));rng=random.Random(78724)

def project(q,drop,keep):return keep if q==drop else q
def transition(q,b,drop,keep,bit,act):
 w,d,z=act if q==keep and b==bit else t[q,b]
 return w,d,project(z,drop,keep)

def oldpath(s,initial):
 out=[];delta={};h=0
 for n in range(a.limit):
  b=delta.get(h,initial[h]);w,d,z=t[s,b]
  if w==initial[h]:delta.pop(h,None)
  else:delta[h]=w
  h+=d;s=z;out.append((s,h,tuple(sorted(delta.items()))))
  if s==254:break
 return out
samples={}
for q in states:
 samples[q]=[]
 for b in(0,1):
  allowed=[dict(g)for g in ctx[q]if 0 not in dict(g)or dict(g)[0]==b]
  if not allowed:continue
  for i in(0,-1):
   g=allowed[i];initial={j:rng.randrange(2)for j in range(-a.limit-5,a.limit+6)};initial.update(g);initial[0]=b
   samples[q].append((initial,oldpath(q,initial)))

def screen(records,drop,keep,bit,act):
 for initial,old in records:
  delta={};s=keep;h=0
  for n in range(a.limit):
   if s==254:return False
   b=delta.get(h,initial[h]);w,d,z=transition(s,b,drop,keep,bit,act)
   if w==initial[h]:delta.pop(h,None)
   else:delta[h]=w
   h+=d;s=z
   if(s,h,tuple(sorted(delta.items())))in old:break
  else:return False
 return True

def exact(oldstate,g,drop,keep,bit,act):
 todo=[(dict(g),(oldstate,0,()),(keep,0,()),(),(),0,0)];branch=0;done=[]
 while todo:
  init,x,y,xh,yh,xn,yn=todo.pop();branch+=1
  if branch>4096:return None
  px=(project(x[0],drop,keep),x[1],x[2])
  if xn>0 and yn>0 and (px in yh or y in xh):done.append((xn,yn));continue
  if xn>=a.limit and yn>=a.limit:return None
  side=0 if(xn<=yn and x[0]!=254)or y[0]==254 else 1
  if side==0 and xn>=a.limit:side=1
  elif side==1 and yn>=a.limit:side=0
  s,h,changes=x if side==0 else y
  if s==254:return None
  dc=dict(changes)
  if h not in init:
   for b in(0,1):
    ni=init.copy();ni[h]=b;todo.append((ni,x,y,xh,yh,xn,yn))
   continue
  b=dc.get(h,init[h]);w,d,z=transition(s,b,drop,keep,bit,act)if side else t[s,b]
  if w==init[h]:dc.pop(h,None)
  else:dc[h]=w
  nc=(z,h+d,tuple(sorted(dc.items())))
  if side==0:todo.append((init,nc,y,xh+((project(z,drop,keep),nc[1],nc[2]),),yh,xn+1,yn))
  else:todo.append((init,x,nc,xh,yh+(nc,),xn,yn+1))
 return {'branches':branch,'leaves':len(done),'old':max(x for x,y in done),'new':max(y for x,y in done)}

results=[];trials=survivors=pairs=0
for drop in sorted(cluster):
 if drop not in states or drop==0:continue
 for keep in states:
  if keep in(0,drop):continue
  pairs+=1;records=[(initial,{(project(s,drop,keep),h,dc)for s,h,dc in old})for q in(drop,keep)for initial,old in samples[q]]
  for bit,w,d,helper in itertools.product((0,1),(0,1),(-1,1),states):
   if helper==drop:continue
   trials+=1;act=(w,d,helper)
   if not screen(records,drop,keep,bit,act):continue
   survivors+=1;checks=[]
   for q in(drop,keep):
    for g in ctx[q]:
     v=exact(q,g,drop,keep,bit,act)
     if v is None:break
     checks.append(v)
    else:continue
    break
   else:
    item={'drop':drop,'keep':keep,'replacement':[bit,*act],'checks':checks};results.append(item);print('HIT',item,flush=True)
 print('drop',drop,'pairs',pairs,'trials',trials,'survivors',survivors,'seconds',time.monotonic()-start,flush=True)
report={'table':str(a.table),'sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'depth':a.depth,'limit':a.limit,'contexts':str(a.contexts) if a.contexts else 'exact finite history','pairs':pairs,'trials':trials,'survivors':survivors,'results':results,'seconds':time.monotonic()-start};a.output.write_text(json.dumps(report,indent=2));print('DONE',len(results),report['seconds'],flush=True)
