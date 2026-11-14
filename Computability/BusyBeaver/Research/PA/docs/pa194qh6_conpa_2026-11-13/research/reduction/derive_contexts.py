#!/usr/bin/env python3
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import argparse,itertools,json
from common import load
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--package-root',type=Path,default=HERE.parents[1]);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
OUT=a.output;OUT.mkdir(parents=True,exist_ok=True);D=a.package_root/'machine'
c,rows,sites,ins,contracts,digest=load(a.package_root)
K=5;patterns=defaultdict(set);seen=set()
@lru_cache(maxsize=200000)
def prefixes(s,k):
 if k==0:return ((),)
 if not s:return ((0,)*k,)
 x,*tail=s;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
 assert x[0]=='r';_,b,a,d=x;assert a>=0 and d>=0
 if a==0:
  if d>=k:return ((b,)*k,)
  return tuple((b,)*d+p for p in prefixes(tail,k-d))
 result=set()
 for n in range(k+1):
  size=a*n+d
  if size>=k:result.add((b,)*k);break
  for p in prefixes(tail,k-size):result.add((b,)*size+p)
 return tuple(result)
def observe(s):
 q,onl,left,right=s
 if q in c.BOXSTATES:return
 lp=prefixes(left,K+1 if onl else K);rp=prefixes(right,K if onl else K+1)
 key=q,onl,lp,rp
 if key in seen:return
 seen.add(key)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1
  patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
r=c.validate(rows,contracts,observe=observe);assert r['ok']
seed=json.loads((D/'receipt.json').read_text())['startup']
ones=set();q=74;head=0
for _ in range(seed['steps']):
 if q not in c.BOXSTATES:patterns[q].add(sum(int(head+i-K in ones)<<i for i in range(2*K+1)))
 w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else -1
assert (q,head,ones)==(seed['state'],seed['head'],set(seed['one_cells']))
ctx=OUT/'QH6-contexts-k5.txt';ctx.write_text(''.join(f'{q} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
receipt={'native_sha256':digest,'radius':K,'contexts':sum(map(len,patterns.values())),'context_states':len(patterns),'symbolic_contracts':r,'startup_steps':seed['steps'],'runs':[]}

(OUT/'contexts-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(receipt)
