"""Owned fresh all-initial-tape finite-window invariant and direct fold census."""
from pathlib import Path
from collections import deque, Counter
import json,hashlib,itertools,time
D=Path(__file__).resolve().parent
BASE=D.parent/'latest219_baseline/candidate-k219'
H=lambda b:hashlib.sha256(b).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,m,z=line.split();assert m in ('L','R')
  t[int(q),int(b)]=(int(w),1 if m=='R' else -1,int(z))
 assert len(t)==438 and len({q for q,b in t})==219
 assert all((q,b) in t for q,b in itertools.product({q for q,b in t},(0,1)))
 return t
def closure(t,n,start=0,halt=254):
 r={q:set() for q in {q for q,b in t}|{halt}};todo=deque();h=n//2;mask=(1<<n)-1
 for x in range(1<<n):r[start].add(x);todo.append((start,x))
 while todo:
  q,x=todo.popleft()
  if q==halt:continue
  w,d,z=t[q,(x>>h)&1];y=(x&~(1<<h))|(w<<h)
  for bit in (0,1):
   v=(y>>1)|(bit<<(n-1)) if d==1 else ((y<<1)&mask)|bit
   if v not in r[z]:r[z].add(v);todo.append((z,v))
 # Independently expressed tuple membership, including arbitrary boundary symbols.
 rt={q:{tuple((x>>i)&1 for i in range(n)) for x in xs}for q,xs in r.items()}
 assert len(rt[start])==1<<n
 checks=0
 for q,xs in rt.items():
  if q==halt:continue
  for x in xs:
   w,d,z=t[q,x[h]];y=list(x);y[h]=w
   for bit in (0,1):
    v=tuple(y[1:]+[bit]) if d==1 else tuple([bit]+y[:-1])
    assert v in rt[z];checks+=1
 return r,checks
def dump(n,x):(D/n).write_text(json.dumps(x,indent=2)+'\n')
def main():
 began=time.monotonic();p=BASE/'k219.native.tm';assert H(p.read_bytes())=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
 t=table(p);r,c=closure(t,7);dump('CLOSURE7.json',r if False else {q:sorted(v)for q,v in r.items()})
 live={q:{b for b in (0,1) if any((x>>3)&1==b for x in r[q])}for q in r}
 hits=[];cnt=Counter();Q=sorted({q for q,b in t}-{0})
 for q in Q:
  for k in Q:
   if q==k:continue
   cnt['pairs']+=1;phi=lambda z:k if z==q else z
   acts=[]
   for b in (0,1):
    a={(w,d,phi(z))for x in (q,k) if b in live[x] for w,d,z in [t[x,b]]}
    if len(a)>1:break
    acts.append(next(iter(a))if a else (b,1,k))
   if len(acts)==2:hits.append(dict(drop=q,keep=k,actions=acts,live=[sorted(live[q]),sorted(live[k])]))
 dump('DIRECT_RESULT.json',dict(status='COMPLETE_DIRECT_ALL_STATE_SCREEN',input_sha256=H(p.read_bytes()),closure_width=7,closure_points=sum(map(len,r.values())),checks=c,counts=dict(cnt),hits=hits,live={q:sorted(v)for q,v in live.items()},seconds=time.monotonic()-began))
 print(json.dumps(dict(points=sum(map(len,r.values())),checks=c,hits=hits,seconds=time.monotonic()-began)))
if __name__=='__main__':main()
