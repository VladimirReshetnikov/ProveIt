#!/usr/bin/env python3
"""Conservative radius-K contexts, including every arithmetic sweep interior.
Uses the exact independent universal runtime, and observes its generic one-block
lemmas as well as all source frames. Opaque contexts deliberately overapproximate.
"""
import sys,json,itertools,functools,time
from pathlib import Path
import argparse
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--family',choices=['194','194C'],default='194')
ap.add_argument('--radius',type=int,default=4)
args=ap.parse_args()
PACKAGE=Path(__file__).resolve().parents[2]
ROOT=PACKAGE/'reference/pa194';K=args.radius
OUT=Path(__file__).resolve().parent
ALT=args.family=='194C';TAG=args.family+'_'
TABLE=PACKAGE/'tables/pa194C.native.tm' if ALT else ROOT/'construction/tables/pa194.native.tm'
SITES=PACKAGE/'source/pa194C.sites.json' if ALT else ROOT/'construction/source/pa194.sites.json'
STARTUP=57922 if ALT else 58154
sys.path.insert(0,str(ROOT/'verification/independent/reference'))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48
rows={}
for line in TABLE.read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
mapping={int(k):v for k,v in json.loads((ROOT/'verification/independent/reference/legacy_mapping.json').read_text()).items()}
for q,b in rows:mapping.setdefault(q,q+10000)
mapping.setdefault(254,254)
back={v:k for k,v in mapping.items()}
table={(mapping[q],b):(w,d,mapping[n]) for(q,b),(w,d,n)in rows.items()}
patterns={q:set() for q,b in rows}
def tup(a):return tuple(tup(x) if isinstance(x,(tuple,list)) else x for x in a)
@functools.lru_cache(maxsize=300000)
def prefixes(atoms,k):
 if k==0:return ((),)
 if not atoms:return ((0,)*k,)
 a,*tail=atoms;tail=tuple(tail)
 if a[0]=='blank':return ((0,)*k,)
 if a[0]=='opaque':return tuple(itertools.product((0,1),repeat=k))
 if a[0]=='run':
  bit,n=a[1:];c=n[0];assert all(x>=0 for x in n)
  if not any(n[1:]):sizes=[min(c,k)]
  elif c>=k:sizes=[k]
  else:sizes=range(c,k+1)
  out=set()
  for z in sizes:
   if z==k:out.add((bit,)*k)
   else:
    for p in prefixes(tail,k-z):out.add((bit,)*z+p)
  return tuple(out)
 if a[0]=='list':
  family,reverse=a[1],a[3];out=set(prefixes(tail,k))
  for v in range(k+1):
   block=[0]+[1]*(v+1) if family=='B' else [1,0]+[1]*v
   if reverse:block=block[::-1]
   if len(block)>=k:out.add(tuple(block[:k]))
   else:
    for p in prefixes(atoms,k-len(block)):out.add(tuple(block)+p)
  return tuple(out)
 raise ValueError(a)
seen=set();obs=0
def observe(q,d,left,right):
 global obs
 left,right=tup(left),tup(right)
 lp=prefixes(left,K+(d==-1));rp=prefixes(right,K+(d==1))
 key=q,d,lp,rp
 if key in seen:return
 seen.add(key);obs+=1
 native=back[q]
 for a,b in itertools.product(lp,rp):
  word=tuple(reversed(a))+b
  assert len(word)==2*K+1
  patterns[native].add(sum(x<<i for i,x in enumerate(word)))
orig=s.State.step
unary_obs=0
def step(self,table,lemmas,clock,motion):
 global unary_obs
 self.key();observe(self.q,self.direction,self.left,self.right)
 src=self.right if self.direction==1 else self.left
 dst=self.left if self.direction==1 else self.right
 if src and src[0][0]=='run':
  a=src[0];w,d,n=table[self.q,a[1]]
  if n==self.q and d==self.direction:
   # Every internal configuration of the accelerated literal self-loop.
   if any(a[2][1:]):splits=[(s.var(1),s.add(s.num(1),s.var(2)))]
   else:splits=[(s.num(j),s.num(a[2][0]-j)) for j in range(1,a[2][0])]
   for passed,remaining in splits:
    ss=[s.run(a[1],remaining)]+src[1:];dd=[s.run(w,passed)]+dst
    observe(self.q,d,dd if d==1 else ss,ss if d==1 else dd);unary_obs+=1
 return orig(self,table,lemmas,clock,motion)
s.State.step=step
start=time.monotonic();lemmas,blocks=s.prove_blocks(table)
sites=json.loads(SITES.read_text())
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
contracts=0;symbolic_steps=0
for i,(pc,op,arg) in enumerate(sites):
 for pos in ([False,True] if op=='dec' else [False]):
  result=s.case(table,lemmas,[pc,ops[op],arg],pos);contracts+=1;symbolic_steps+=result['symbolic_steps']
 if(i+1)%1000==0:print(i+1,'sites',time.monotonic()-start,flush=True)
# Full literal startup, including arithmetic controls.
ones=set();q=74;h=0
for n in range(STARTUP):
 patterns[q].add(sum(int(h+j-K in ones)<<j for j in range(2*K+1)))
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
assert(q,h)==(84,-2)
(OUT/f'{TAG}symbolic_patterns_k{K}.txt').write_text(''.join(f'{q} {v}\n' for q in sorted(patterns)for v in sorted(patterns[q])))
receipt={'K':K,'contracts':contracts,'symbolic_steps':symbolic_steps,'list_lemmas':len(blocks),'distinct_observations':obs,'unary_internal_observations':unary_obs,'total_patterns':sum(map(len,patterns.values())),'counts':{q:len(v)for q,v in patterns.items()},'seconds':time.monotonic()-start,'scope':'Conservative universal source-frame and exact startup local contexts, including generic one-block proofs and unary acceleration interiors.'}
(OUT/f'{TAG}symbolic_patterns_k{K}.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
