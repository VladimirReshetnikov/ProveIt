#!/usr/bin/env python3
"""Collect heuristic reduction windows from source, sampled boxes, and startup."""
from pathlib import Path
import sys,json,itertools,functools,collections,time
HERE=Path(__file__).resolve().parent
import importlib.util
if len(sys.argv)<8:
 raise SystemExit('usage: collect_contexts.py table.native.tm sites.json instructions.json out.txt radius runtime.py startup_steps')
table,sites_path,ins_path,out=map(Path,sys.argv[1:5]);K=int(sys.argv[5]);runtime_path=Path(sys.argv[6]);startup_steps=int(sys.argv[7])
spec = importlib.util.spec_from_file_location('symbolic_runtime', runtime_path)
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
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
 if x[0]=='x':
  _,kind,r=x
  # The first k+1 blocks suffice for a k-cell prefix.
  def rec(j,acc):
   if len(acc)>=k:return {tuple(acc[:k])}
   ans=set()
   for v in range(k+1):
    block=[0]+[1]*(v+1)
    if kind=='mark' and j==r:block[1]=0
    ans.update(rec(j+1,acc+block))
   return ans
  return tuple(rec(0,[]))
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
 # Skip only the start of an oracle call, whose body is covered literally below.
 if not onl and len(r)==1 and r[0][0]=='x' and c.oracle(q,None,r[0]) is not None:return
 if not onl and len(r)==1 and r[0][0]=='x' and q==0 and r[0][1]=='mark':return
 scan_interiors(s)
 lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
 key=q,onl,lp,rp
 if key in seen:return
 seen.add(key)
 add_windows(q,onl,lp,rp)
result=c.validate(rows,cs,observe=observe);assert result['ok'],result
# Literal box traces. This is a candidate screen, not a proof of coverage.
import random
rng=random.Random(20261114)
files=[]
for v in range(2*K+3):
 files.append([v]*10)
 for j in range(10):
  vs=[0]*10;vs[j]=v;files.append(vs)
for trial in range(3000):
 files.append([rng.randrange(2*K+3) for _ in range(rng.randrange(10,14))])
def collect_run(q,ones,stop,limit=100000):
 h=0
 for z in range(limit):
  p=sum(int(h+i-K in ones)<<i for i in range(2*K+1));patterns[q].add(p)
  w,d,n=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1;q=n
  if stop(q,h):return
 raise ValueError(('run failed',q,h))
for vs in files:
 tape={-1};pos=0;starts=[]
 for v in vs:
  starts.append(pos);tape.update(range(pos+1,pos+v+2));pos+=v+2
 for r in range(9):
  collect_run(c.SK[r],set(tape),lambda q,h:q==(1 if r==0 else 3) and h==-1)
  marked=set(tape);marked.remove(starts[r]+1)
  collect_run(64,set(marked),lambda q,h:q==40 and h==-1)
  collect_run(0,set(marked),lambda q,h:(q,h)==((97,-1) if vs[r]==0 else (40,0)))
# Blank trace through the exact known source entry.
ones=set();q=74;h=0
for z in range(startup_steps):
 p=sum(int(h+i-K in ones)<<i for i in range(2*K+1));patterns[q].add(p)
 w,d,n=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1;q=n
assert (q,h)==(84,-2),(q,h)
expected={h-1,h+48};expected.update(h+i for i,b in enumerate(sites[25][0]) if b=='1')
pos=h+49
for value in [0,0,0,0,0,0,2,0,0]+[1]*26:
 pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
assert ones==expected,'Startup does not equal the complete prescribed source frame'
out.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
print(json.dumps({'validation':result,'radius':K,'contexts':sum(map(len,patterns.values())), 'startup_steps':startup_steps, 'startup_whole_frame_checked':True,
                  'accelerated_scan_observations':scan_observations,
                  'scope':'Symbolic source windows plus sampled arithmetic interiors and exact blank prefix. Heuristic screen, not a certified reachability invariant.'},indent=2))
