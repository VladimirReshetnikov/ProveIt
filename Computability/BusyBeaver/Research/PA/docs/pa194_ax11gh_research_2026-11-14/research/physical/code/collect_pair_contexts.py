"""Conservative radius-ten windows for two targeted pair-fusion screens."""
from common import c,load_case
from pathlib import Path
import sys,json,itertools,functools
K=int(sys.argv[1]);out=Path(sys.argv[2]);rows,sites,ins,cs=load_case('primary')
@functools.lru_cache(None)
def prefixes(s,k):
 if k==0:return ((),)
 if not s:return ((0,)*k,)
 x,*tail=s;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
 if x[0]=='r':
  _,b,a,d=x
  if a==0:
   if d>=k:return ((b,)*k,)
   return tuple((b,)*d+p for p in prefixes(tail,k-d))
  ret=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:ret.add((b,)*k);break
   for p in prefixes(tail,k-size):ret.add((b,)*size+p)
  return tuple(ret)
 raise ValueError(x)
seen=set();pat=set()
def obs(s):
 q,onl,l,r=s
 if q not in (16,122,88,301,51):return
 if c.headbit(l if onl else r)!=0:return
 if s in seen:return
 seen.add(s)
 lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1
  pat.add((q,sum(bit<<i for i,bit in enumerate(tape))))
res=c.validate(rows,cs,observe=obs)
# exact canonical startup plus its complete finite tape
q,h,t=74,0,set()
for step in range(58154):
 b=int(h in t)
 if q in (16,122,88,301,51) and b==0:
  pat.add((q,sum(int(i+h-K in t)<<i for i in range(2*K+1))))
 w,d,q=rows[q,b];(t.add if w else t.discard)(h);h+=1 if d else -1
out.write_text(''.join(f'{q} {p}\n' for q,p in sorted(pat)))
print(json.dumps(dict(validation=res,radius=K,symbolic_configs=len(seen),contexts=len(pat),per_q={str(q):sum(x==q for x,p in pat) for q in (16,122,88,301,51)})))
