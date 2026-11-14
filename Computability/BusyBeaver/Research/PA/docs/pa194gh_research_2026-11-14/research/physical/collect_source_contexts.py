#!/usr/bin/env python3
"""Collect complete symbolic source contexts, intentionally excluding startup."""
from pathlib import Path
import sys,json,itertools,functools,collections,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE / "vendor"))
import symbolic_runtime as c
table,sites_path,ins_path,out=map(Path,sys.argv[1:5]);K=int(sys.argv[5]) if len(sys.argv)>5 else 4
c.PHYSICAL[:]=[6,2,0,4,3,7,8,5,1]
sites=json.loads(sites_path.read_text());ins=json.loads(ins_path.read_text());rows={}
for ln in table.read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
cs=[]
def frame(i,extra=0,effect=c.PLAIN):return c.frame(tuple(map(int,sites[i][0])),extra,effect)
def target(i,extra=0,effect=c.PLAIN):return c.canonical(frame(i,extra,effect))
for i,code in enumerate(ins):
 st=frame(i)
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,target(n,0,('x','inc',c.PHYSICAL[r]))))
 elif code[0]=='dec':
  _,r,z,p=code;cs.append((i,(c.PHYSICAL[r],True),st,target(z)));cs.append((i,(c.PHYSICAL[r],False),st,target(p,1,('x','dec',c.PHYSICAL[r]))))
 elif code[0]=='jump':cs.append((i,None,st,target(code[1])))
 else:cs.append((i,None,st,None))
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
out.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
print(json.dumps({'validation':result,'radius':K,'contexts':sum(map(len,patterns.values())),
                  'accelerated_scan_observations':scan_observations,
                  'scope':'source only; startup intentionally excluded; arithmetic engine not narrowed'},indent=2))
