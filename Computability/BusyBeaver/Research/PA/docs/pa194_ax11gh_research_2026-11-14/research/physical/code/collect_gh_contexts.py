"""Conservative complete source/startup windows including unary scan interiors."""
from common import c,load_case
from pathlib import Path
import sys,json,itertools,functools,collections
K=int(sys.argv[1]);out=Path(sys.argv[2]);rows,sites,ins,cs=load_case('gh')
@functools.lru_cache(maxsize=200000)
def prefixes(s,k):
 if k==0:return ((),)
 if not s:return ((0,)*k,)
 x,*tail=s;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
 if x[0]=='r':
  _,b,a,d=x;assert a>=0 and d>=0
  if a==0:
   if d>=k:return ((b,)*k,)
   return tuple((b,)*d+p for p in prefixes(tail,k-d))
  out=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:out.add((b,)*k);break
   for p in prefixes(tail,k-size):out.add((b,)*size+p)
  return tuple(out)
 raise ValueError(x)
patterns=collections.defaultdict(set);seen=set();seen_scans=set();scan_observations=0
def add_windows(q,onl,lp,rp):
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1;patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
def scan_interiors(s):
 """All interior positions of each accelerated constant-symbol self-loop.

 For a radiusK window, a run longer than2K+1 is indistinguishable from
 length2K+1 after considering positions near both ends and the middle.
 Correlations between external stream parameters are deliberately discarded.
 """
 global scan_observations
 q,onl,l,r=s;stream=l if onl else r
 if not stream or stream[0][0]!='r':return
 _,b,a,d=stream[0];act=rows.get((q,b))
 if act is None or act[1]==onl or act[2]!=q:return
 if s in seen_scans:return
 seen_scans.add(s);scan_observations+=1
 w=act[0];lengths=[];cap=2*K+1
 if a==0:lengths=[min(d,cap)]
 else:
  for n in range(cap+1):
   z=a*n+d;lengths.append(min(z,cap))
   if z>=cap:break
 for length in set(lengths):
  for consumed in range(length):
   remaining=length-consumed
   if onl:
    lp=prefixes((('r',b,0,remaining),)+l[1:],K+1)
    rp=prefixes((('r',w,0,consumed),)+r,K)
   else:
    lp=prefixes((('r',w,0,consumed),)+l,K)
    rp=prefixes((('r',b,0,remaining),)+r[1:],K+1)
   add_windows(q,onl,lp,rp)
def observe(s):
 q,onl,l,r=s
 if q in c.BOXSTATES:return
 scan_interiors(s)
 lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
 key=q,onl,lp,rp
 if key in seen:return
 seen.add(key)
 add_windows(q,onl,lp,rp)
result=c.validate(rows,cs,observe=observe);assert result['ok'],result
startup_steps=57922
ones=set();q=74;head=0
for _ in range(startup_steps):
 if q not in c.BOXSTATES:
  patterns[q].add(sum(int(head+i-K in ones)<<i for i in range(2*K+1)))
 w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else -1
assert q==84 and head==-2
out.write_text(''.join(f'{q} {p}\n'  for q in sorted(patterns) for p in sorted(patterns[q])))
print(json.dumps({'validation':result,'radius':K,'contexts':sum(map(len,patterns.values())),
                  'accelerated_scan_observations':scan_observations,
                  'startup_steps':startup_steps, 'scope':'source and startup; arithmetic engine not narrowed'},indent=2))
