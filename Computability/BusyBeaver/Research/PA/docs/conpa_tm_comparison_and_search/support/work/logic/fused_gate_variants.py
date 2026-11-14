#!/usr/bin/env python3
"""Bootstrap-safe gate fusion variants and deterministic grammar screening.

h5 may be moved into the guarded gate because it does not depend on A.
Moving h1 also requires a separate explosion head: the old h1 is the source
of explosion, so blindly using conjunction projections would be circular.
"""
import word_variants as v
import sys,time,json,itertools,collections,random
from pathlib import Path
OUT=v.BASE/'work/logic/fused_gate_variants';OUT.mkdir(exist_ok=True)
PROFILES={'h5':((4,),False),'h1_explosion':((0,),True),'both_explosion':((0,4),True)}

def parts(flags,flip,profile):
 hs=v.heads(flags,flip);fused,expl=PROFILES[profile]
 kept=[h for j,h in enumerate(hs)if j not in fused]
 if expl:kept.insert(0,v.I(v.ONE,'H'))
 g=v.gate(False,flip);_,inner,one=g
 _,delta,(_,vac,q)=inner
 terms=[hs[j]for j in fused]+[delta,vac]
 return list(map(v.emit,kept)),list(map(v.emit,terms)),v.emit(q)

def makeword(kept,terms,q,ho,go):
 return v.prefix+sum((kept[j]for j in ho),[])+sum((terms[j]for j in go),[])+q+['node65']*len(terms)+['node49',v.INC,'node65']+v.suffix

def repair(word,seed=0):
 rng=random.Random(seed);seq=[v.leafid[x]for x in word];rules=[]
 while len(seq)>1:
  counts=collections.Counter(zip(seq,seq[1:]))
  if max(counts.values())<2:
   def cat(a):
    if len(a)==1:return a[0]
    k=len(a)//2;p=cat(a[:k]),cat(a[k:]);i=len(v.leafnames)+len(rules);rules.append(p);return i
   rt=cat(seq);break
  pair=max(counts,key=lambda p:counts[p]+(rng.random()if seed else 0))
  x=len(v.leafnames)+len(rules);rules.append(pair);out=[];i=0
  while i<len(seq):
   if i+1<len(seq)and(seq[i],seq[i+1])==pair:out.append(x);i+=2
   else:out.append(seq[i]);i+=1
  seq=out
 else:rt=seq[0]
 cache=list(v.leafnames)
 for a,b in rules:cache.append((cache[a],cache[b]))
 return len(rules),cache[rt]

def variants(profile):
 for mf,ef,flags in itertools.product((False,True),(False,True),range(8)):
  v.M=(lambda a,b:v.C(1,b,a))if mf else(lambda a,b:v.C(1,a,b))
  kept,terms,q=parts(flags,ef,profile)
  for ho in itertools.permutations(range(len(kept))):
   for go in itertools.permutations(range(len(terms))):
    meta={'profile':profile,'memflip':mf,'eqflip':ef,'antecedent_flags':flags,'head_order':ho,'gate_order':go}
    yield meta,makeword(kept,terms,q,ho,go)

if __name__=='__main__':
 profiles=sys.argv[1:]or list(PROFILES)
 for profile in profiles:
  kept,terms,q=parts(0,False,profile)
  baseword=makeword(kept,terms,q,range(len(kept)),range(len(terms)))
  (OUT/(profile+'.word.json')).write_text(json.dumps({'profile':profile,'word':baseword,'stack_items':9-len(PROFILES[profile][0])+int(PROFILES[profile][1])},indent=2))
  print('PROFILE',profile,'tokens',len(baseword),flush=True)
  start=time.monotonic();best=999;effbest=62;hist=collections.Counter();count=0;top=[]
  for meta,w in variants(profile):
   n,t=repair(w);hist[n]+=1;count+=1
   if n<best:
    best=n;print('NEW DAG',profile,n,meta,'seconds',time.monotonic()-start,flush=True)
    (OUT/(profile+f'_{n}.grammar.json')).write_text(json.dumps(v.encode(t),indent=2))
    (OUT/(profile+f'_{n}.meta.json')).write_text(json.dumps({'meta':meta,'word':w},indent=2))
   if n<=70:
    r,idx,sh=v.build(t);ops=v.opportunities_fast(r,sh);match=v.max_matching(ops);eff=n-len(match)
    if eff<effbest:
     effbest=eff;print('NEW EFFECTIVE',profile,eff,'DAG',n,'folds',match,meta,flush=True)
     (OUT/(profile+f'_effective_{eff}.grammar.json')).write_text(json.dumps(v.encode(t),indent=2))
     (OUT/(profile+f'_effective_{eff}.meta.json')).write_text(json.dumps({'meta':meta,'matching':match,'word':w},indent=2))
   if n<=best+1:top.append((n,meta))
   if count%10000==0:print('PROGRESS',profile,count,'DAGbest',best,'effbest',effbest,'seconds',time.monotonic()-start,flush=True)
  (OUT/(profile+'_results.json')).write_text(json.dumps({'histogram':hist,'DAGbest':best,'effectivebest':effbest,'count':count,'top':[p for p in top if p[0]<=best+1]},indent=2))
  print('DONE',profile,count,best,effbest,'seconds',time.monotonic()-start,flush=True)
