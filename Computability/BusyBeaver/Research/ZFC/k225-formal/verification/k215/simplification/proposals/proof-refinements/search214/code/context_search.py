from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import itertools,json,time
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
 import argparse,hashlib,sys
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O; assertions are required.')
 ap=argparse.ArgumentParser(description='Bounded one-row merge synthesis on a native binary TM table. No completeness or minimum-state claim.')
 ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--depth',type=int,default=4);ap.add_argument('--steps',type=int,default=45);ap.add_argument('--nodes',type=int,default=200)
 a=ap.parse_args();assert a.depth>=0 and a.steps>0 and a.nodes>0
 started=time.time();T=read(a.table);Q=sorted({q for q,b in T})
 assert len(T)==2*len(Q) and all((q,b)in T for q in Q for b in(0,1)) and {z for w,d,z in T.values()}-set(Q)=={254}
 C=contexts(T,Q,a.depth);pairs=[];survivors=[];tested=0
 for q,r in itertools.combinations(Q,2):
  if q==0:continue
  for b in(0,1):
   if T[q,1-b]!=T[r,1-b] or T[q,b]==T[r,b]:continue
   cq=[dict(c)for c in C[q]if dict(c).get(0,b)==b];cr=[dict(c)for c in C[r]if dict(c).get(0,b)==b]
   if not cq or not cr or any(compatible(x,y)for x in cq for y in cr):continue
   pairs.append((q,r,b,cq,cr))
 for q,r,b,cq,cr in pairs:
  for w,d,h in itertools.product((0,1),(-1,1),Q):
   tested+=1;action=(w,d,h);proof=[]
   for v,cs in[(q,cq),(r,cr)]:
    for c in cs:
     result=block(T,v,r if v==q else q,b,action,c,limit=a.steps,maxnodes=a.nodes)
     if result is None:break
     proof.append((v,c,result))
    else:continue
    break
   else:survivors.append({'keep':q,'drop':r,'read':b,'action':action,'proof':proof})
 assert tested==len(pairs)*len(Q)*4
 report={'status':'BOUNDED_SEARCH_NO_SURVIVOR'if not survivors else'BOUNDED_SEARCH_SURVIVORS_REQUIRE_REVIEW','table':a.table.name,'table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'working_states':len(Q),'backward_context_depth':a.depth,'maximum_literal_steps_per_block':a.steps,'maximum_symbolic_nodes_per_block':a.nodes,'eligible_pairs':[[q,r,b]for q,r,b,cq,cr in pairs],'specifications':tested,'survivors':survivors,'seconds':time.time()-started,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'One-row merges with the other row literally shared and finite graph-derived tape contexts. Search bounds restrict this family; no global impossibility or state-count lower bound follows.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k not in('eligible_pairs','survivors')},indent=2))
