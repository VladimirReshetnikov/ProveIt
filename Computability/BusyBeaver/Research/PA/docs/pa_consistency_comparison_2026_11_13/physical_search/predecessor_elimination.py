#!/usr/bin/env python3
"""Delete single-incoming states using two-step parent blocks (exact finite windows)."""
from pathlib import Path
from collections import defaultdict, deque
import json, time, argparse, hashlib

P=Path(__file__).resolve().parent/'reference/pa196/data/pa196.tm'

def read(path):
 t={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return t

def closure(t,R):
 W=2*R+1;MASK=(1<<W)-1;MID=1<<R
 seen={(0,0)};todo=deque(seen);ctx=defaultdict(list)
 while todo:
  q,a=todo.popleft();b=(a>>R)&1;w,d,n=t[q,b]
  ctx[q,b].append(a)
  a=(a|MID) if w else (a&~MID)
  if n==196:continue
  for f in (0,1):
   a1=((a>>1)|(f<<(W-1))) if d==1 else (((a<<1)&MASK)|f)
   k=n,a1
   if k not in seen:seen.add(k);todo.append(k)
 return ctx,len(seen)

def old2(t,qp,bp,a,R):
 h=R;q=qp
 for _ in range(2):
  b=(a>>h)&1;w,d,q=t[q,b];a=(a|(1<<h)) if w else (a&~(1<<h));h+=d
 return a,h,q

def check(t,drop,qp,bp,patch,a,goal,R,steps=32):
 mask,h,q= a,R,qp
 for k in range(1,steps+1):
  if h<0 or h>2*R or q==196 or q==drop:return None
  b=(mask>>h)&1
  w,d,q=patch if q==qp and b==bp else t[q,b]
  mask=(mask|(1<<h)) if w else (mask&~(1<<h));h+=d
  if (mask,h,q)==goal:return k
 return None

def scan(t,ctx,R,steps=32):
 incoming=defaultdict(list)
 for k,(_,_,v) in t.items():incoming[v].append(k)
 candidates=[(drop,prev[0]) for drop,prev in incoming.items() if drop not in (0,196) and len(prev)==1 and prev[0][0]!=drop]
 out=[];count=0
 for drop,(qp,bp) in sorted(candidates):
  cases=[(a,old2(t,qp,bp,a,R)) for a in ctx[qp,bp]]
  for n in range(197):
   if n==drop:continue
   for d in (-1,1):
    for w in (0,1):
     patch=w,d,n;count+=1;ks=[]
     for a,goal in cases:
      k=check(t,drop,qp,bp,patch,a,goal,R,steps)
      if k is None:break
      ks.append(k)
     else:
      if cases:
       z={'drop':drop,'parent_row':[qp,bp],'patch':[w,'R' if d==1 else'L',n],'lengths':sorted(set(ks)),'cases':len(cases)}
       out.append(z);print('SURVIVOR',z,flush=True)
  print('done',drop,'of',len(candidates),'contexts',len(cases),'patches',count,flush=True)
 return out,candidates,count

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=3);ap.add_argument('--steps',type=int,default=32);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 start=time.monotonic();t=read(P);ctx,N=closure(t,a.radius);print('closure',N,flush=True)
 out,cases,count=scan(t,ctx,a.radius,a.steps)
 receipt={'source_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'template':'one incoming row replaced, old two-step block','radius':a.radius,'max_steps':a.steps,'closure_configurations':N,'drop_candidates':len(cases),'tested_patches':count,'survivors':out,'elapsed_seconds':time.monotonic()-start}
 a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
if __name__=='__main__':main()
