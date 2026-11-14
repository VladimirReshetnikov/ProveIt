#!/usr/bin/env python3
import sys,time,json,random,collections,itertools
from pathlib import Path
import word_variants as v
memflip=len(sys.argv)>1 and sys.argv[1]=='memflip'
if memflip:v.M=lambda a,b:v.C(1,b,a)
OUT=v.BASE/('work/logic/repair_variants_memflip'if memflip else'work/logic/repair_variants');OUT.mkdir(exist_ok=True)
leafnames=v.leafnames;leafid=v.leafid
start=time.monotonic();best=1000;best_eff=62;hist=collections.Counter();screened=[]
def repair(word,seed=0):
 rng=random.Random(seed);seq=[leafid[x]for x in word];rules=[]
 while len(seq)>1:
  counts=collections.Counter(zip(seq,seq[1:]))
  if max(counts.values())<2:
   # Balanced final concatenation; no repeated bigram remains.
   def cat(a):
    if len(a)==1:return a[0]
    k=len(a)//2;p=(cat(a[:k]),cat(a[k:]));i=len(leafnames)+len(rules);rules.append(p);return i
   rt=cat(seq);break
  pair=max(counts,key=lambda p:counts[p]+(rng.random()if seed else 0))
  x=len(leafnames)+len(rules);rules.append(pair);out=[];i=0
  while i<len(seq):
   if i+1<len(seq)and(seq[i],seq[i+1])==pair:out.append(x);i+=2
   else:out.append(seq[i]);i+=1
  seq=out
 else:rt=seq[0]
 cache=list(leafnames)
 for a,b in rules:cache.append((cache[a],cache[b]))
 return len(rules),cache[rt]

for j,(meta,word)in enumerate(v.variants()):
 n,t=repair(word,0);hist[n]+=1
 if n<best:
  best=n;print('REPAIR DAG BEST',n,meta,'seconds',time.monotonic()-start,flush=True)
  (OUT/f'dag_{n}.grammar.json').write_text(json.dumps(v.encode(t),indent=2))
  (OUT/f'dag_{n}.meta.json').write_text(json.dumps(meta,indent=2))
 if n<=70:
  r,idx,sh=v.build(t);ops=v.opportunities_fast(r,sh);matching=v.max_matching(ops);eff=n-len(matching)
  if eff<best_eff:
   best_eff=eff;print('EFFECTIVE BEST',eff,'DAG',n,'matching',matching,meta,flush=True)
   (OUT/f'effective_{eff}.grammar.json').write_text(json.dumps(v.encode(t),indent=2))
   (OUT/f'effective_{eff}.meta.json').write_text(json.dumps({'meta':meta,'matching':matching},indent=2))
  if n<=68:screened.append((n,meta,word))
 if j%1000==0:print('progress',j,'best',best,'effective',best_eff,'seconds',time.monotonic()-start,flush=True)
(OUT/'results.json').write_text(json.dumps({'best_DAG':best,'best_effective':best_eff,'histogram':hist,'screened':screened},indent=2))
print('DONE',best,best_eff,'seconds',time.monotonic()-start,flush=True)
