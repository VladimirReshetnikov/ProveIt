#!/usr/bin/env python3
"""Sound context overapproximation from symbolic primitive traces and startup.

Decoder contexts only: states used by opaque box contracts or unary self-loops
are conservatively assigned the entire blank-window invariant instead.
"""
from pathlib import Path
from functools import lru_cache
import sys,json,time,hashlib
from collections import defaultdict
HERE=Path(__file__).resolve().parent
ROOT=HERE
VERIFY=ROOT/'verification'
sys.path.insert(0,str(VERIFY));import symbolic as s
from predecessor_elimination import read,closure,P

@lru_cache(None)
def prefixes(atoms,n):
 if n==0:return frozenset({()})
 if not atoms:return frozenset({(0,)*n})
 x,*tail=atoms;tail=tuple(tail)
 if x[0]=='b':return frozenset((x[1],)+t for t in prefixes(tail,n-1))
 if x[0]=='x':return frozenset(tuple((w>>j)&1 for j in range(n)) for w in range(1<<n))
 _,b,a,c=x
 counts=[min(c,n)] if not a else range(min(c,n),n+1)
 return frozenset((b,)*k+t for k in counts for t in prefixes(tail,n-k))

def collect(R=2):
 inv={q:i for i,q in enumerate(s.labels)};ctx=defaultdict(set)
 protected={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
 protected|={q for (q,b),(w,d,t) in s.rows.items()if q==t}
 protected_dense={inv[q] for q in protected if q in inv}
 def visit(st):
  q,on,l,r=st
  if q in protected:return
  assert not on and r[0][0]=='b'
  left=prefixes(tuple(l),R);right=prefixes(tuple(r),R+1)
  q=inv[q]
  for a in left:
   for b in right:
    bits=a[::-1]+b;mask=sum(x<<i for i,x in enumerate(bits));ctx[q,b[0]].add(mask)
 begin=time.monotonic();ok,detail=s.validate(s.rows,visit)
 assert ok,detail
 t=read(P);full,N=closure(t,R)
 for k,v in full.items():
  if k[0]in protected_dense:ctx[k].update(v)
 ones=set();q=0;h=0
 for step in range(58154):
  bits=tuple(int(h+i in ones)for i in range(-R,R+1));ctx[q,bits[R]].add(sum(x<<i for i,x in enumerate(bits)))
  w,d,q=t[q,bits[R]]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 physical=[0,0,0,0,0,0,2,0,0]+[1]*26
 right=[1]+[0]*47+[1]+[b for v in physical for b in [0]+[1]*(v+1)]
 wanted={-1}|{i for i,b in enumerate(right)if b}
 assert q==75 and {i-h for i in ones}==wanted, 'exact clean startup frame'
 assert s.SITES[25][0]==(1,0,0,0,0,0)
 assert all(ctx[k]<=set(full[k])for k in ctx), 'strong contexts should refine blank invariant'
 out={'radius':R,'input_table_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'source_contracts':detail,'opaque_or_selfloop_states':sorted(protected_dense),'contexts':{f'{q},{b}':sorted(ctx[q,b])for q in range(196)for b in (0,1)},'count':sum(map(len,ctx.values())),'coarse_count':N,'seconds':time.monotonic()-begin}
 return out
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=2);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=collect(a.radius);a.output.write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k!='contexts'})
