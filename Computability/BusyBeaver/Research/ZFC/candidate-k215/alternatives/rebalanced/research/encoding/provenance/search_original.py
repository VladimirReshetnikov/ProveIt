from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import itertools,json,time
Z=Path('/workspace/scratch/1d1a80d76be0/ProveIt/Computability/BusyBeaver/Research/ZFC')
def read(p):
 T={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,n=l.split();T[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
 return T

def block(T,oldq,otherq,b,act,initial,limit=45,maxnodes=200):
 keep=min(oldq,otherq);drop=max(oldq,otherq)
 def mp(q):return keep if q==drop else q
 w0,d0,t0=T[oldq,b];goal=mp(t0)
 initial=dict(initial)
 if 0 in initial and initial[0]!=b:return []
 initial[0]=b
 goalchange={0:w0} if w0!=b else {}
 todo=[(0,keep,{},initial,0)]
 nodes=0;success=[]
 while todo:
  h,q,tape,known,n=todo.pop();nodes+=1
  if nodes>maxnodes:return None
  if n and h==d0 and q==goal and tape==goalchange:
   success.append(n);continue
  if n>=limit or q==254:return None
  if h in tape:vals=[tape[h]]
  elif h in known:vals=[known[h]]
  else:vals=[0,1]
  for b1 in vals:
   kn=dict(known);kn.setdefault(h,b1)
   a=act if (q,b1)==(keep,b) else T.get((q,b1))
   if a is None:return None
   w,d,z=a;z=mp(z);tp=dict(tape)
   if w==kn[h]:tp.pop(h,None)
   else:tp[h]=w
   todo.append((h+d,z,tp,kn,n+1))
 return success

def contexts(T,Q,depth=5):
 inc=defaultdict(list)
 for (q,b),(w,d,t)in T.items():inc[t].append((q,b,w,d))
 @lru_cache(None)
 def pre(q,n):
  if n==0 or q==0:return ((),)
  out=set()
  for p,b,w,d in inc[q]:
   for ctx in pre(p,n-1):
    # Prior configuration known relative tape bits, arrival writes w and shifts by d.
    ctx=dict(ctx)
    if 0 in ctx and ctx[0]!=b:continue
    ctx[0]=w
    ctx={h-d:v for h,v in ctx.items()}
    out.add(tuple(sorted(ctx.items())))
  return tuple(sorted(out))
 return {q:pre(q,depth)for q in Q}

def compatible(a,b):return all(x not in b or b[x]==v for x,v in a.items())
if __name__=='__main__':
 started=time.time();import sys;table=Path(sys.argv[1]) if len(sys.argv)>1 else Z/'candidate-k215/k215.native.tm';T=read(table);Q=sorted({q for q,b in T});C=contexts(T,Q,4)
 out=[];pairs=[]
 for q,r in itertools.combinations(Q,2):
  if q==0:continue
  for b in (0,1):
   if T[q,1-b]!=T[r,1-b]:continue
   if T[q,b]==T[r,b]:continue
   # Conflicting current-known b can eliminate cases. If cross compatible context exists cannot distinguish.
   cq=[dict(c)for c in C[q]if dict(c).get(0,b)==b];cr=[dict(c)for c in C[r]if dict(c).get(0,b)==b]
   if not cq or not cr:continue
   if any(compatible(x,y)for x in cq for y in cr):continue
   pairs.append((q,r,b,cq,cr))
 print(table.name,'pairs',len(pairs),flush=True)
 for q,r,b,cq,cr in pairs:
  for w,d,h in itertools.product((0,1),(-1,1),Q):
   a=(w,d,h)
   z=[]
   for v,cs in[(q,cq),(r,cr)]:
    for c in cs:
     tr=block(T,v,r if v==q else q,b,a,c)
     if tr is None:break
     z.append((v,c,tr))
    else:continue
    break
   else:
    result={'keep':q,'drop':r,'read':b,'action':a,'proof':z};out.append(result);print('FOUND',q,r,b,a,flush=True)
 print('done',time.time()-started,'found',len(out),flush=True)
 (Path('/workspace/scratch/1d1a80d76be0/experiments/encoding')/(table.stem+'_context_folds.json')).write_text(json.dumps(out,indent=2))
