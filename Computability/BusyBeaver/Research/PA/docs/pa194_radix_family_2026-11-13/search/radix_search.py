from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/"construction"))
from functools import lru_cache
import compiler as c
import itertools, json, time
BASE=Path(__file__).resolve().parent
I=0;II=(0,0)
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
g=c.read_grammar(ROOT/'construction/inputs/pa194.grammar.json');raw,_,_=c.build(g)
folds=json.loads((ROOT/'construction/inputs/pa194.folds.json').read_text())
for a,b,act in folds:raw=c.fold(raw,a,b,act)
@lru_cache(None)
def size(t):return 1 if t==0 else size(t[0])+size(t[1])
@lru_cache(None)
def nodes(t):return frozenset()if t==0 else frozenset({t})|nodes(t[0])|nodes(t[1])
frontier={frozenset((I,II))};roots=set()
for depth in range(4):
 nxt=set()
 for pool in frontier:
  for a,b in itertools.product(pool,repeat=2):
   t=(a,b)
   if t in pool:continue
   if size(t)>32:continue
   roots.add(t)
   if depth<3:nxt.add(pool|{t})
 frontier=nxt
 print('GENERATE',depth+1,len(roots),len(frontier),flush=True)
print('ROOTS',len(roots),flush=True)

def compile(t):
 mapping={I:61,II:99,t:190};newrows=dict(raw)
 for n in sorted(nodes(t)-{II,t},key=lambda x:(size(x),repr(x))):mapping[n]=330+len(mapping)-3
 for n,q in mapping.items():
  if n in(I,II):continue
  for bit,ch in enumerate(n):newrows[q,bit]=(bit,True,mapping[ch])
 return newrows,len(mapping)-3,mapping
counts={};best=999;start=time.time();candidates=[]
for i,t in enumerate(sorted(roots,key=lambda t:(len(nodes(t)),size(t),repr(t)))):
 k=size(t)
 if k<4:continue
 rows,extra,mapping=compile(t)
 ops=c.opportunities_fast(rows,{q:None for q,b in rows})
 match=c.max_matching(ops)
 cost=len(rows)//2-len(match)
 counts[cost]=counts.get(cost,0)+1
 if cost<best:
  best=cost;print('BEST',best,'radix',k,'extra',extra,'folds',len(match),'tree',t,'ops',ops,flush=True)
 if cost<=194:
  record={'radix':k,'tree':t,'raw_states':len(rows)//2,'matching':match,'ops':ops,'mapping':[(n,q)for n,q in mapping.items()],'optimistic_states':cost}
  candidates.append(record)
 if i and i%2000==0:print('PROGRESS',i,'elapsed',time.time()-start,'candidates',len(candidates),flush=True)
(BASE/'radix_candidates_replayed.json').write_text(json.dumps(candidates,indent=2))
print('FINISH',len(roots),counts,'candidates',len(candidates),'elapsed',time.time()-start,flush=True)
