#!/usr/bin/env python3
"""Search permutations of parameters within universally instantiated heads."""
import itertools,time,json,sys,random,heapq
from pathlib import Path
import search_grammar as search
from permute_heads import ORIG,HEADS,PREFIX,SUFFIX

PERMS=list(itertools.permutations('ADH'))
VARIANTS=[[list(''.join(h).translate(str.maketrans('ADH',''.join(p)))) for p in PERMS] for h in HEADS]

def makeword(key):
    order=key[:6];variants=key[6:]
    return PREFIX+sum((VARIANTS[i][variants[i]] for i in order),[])+SUFFIX

if __name__=='__main__':
    start=time.time();best=1000;rng=random.Random(123095)
    trials=int(sys.argv[1]) if len(sys.argv)>1 else 100000
    initial=tuple(range(6))+(0,)*6;pool=[(1000,initial)]
    scores={}
    for trial in range(trials):
        if trial<100 or rng.random()<.04:
            order=rng.sample(range(6),6);vs=[rng.randrange(6) for i in range(6)]
            key=tuple(order+vs)
        else:
            key=list(rng.choice(pool[:min(len(pool),100)])[1])
            for _ in range(rng.choices([1,2,3,4],[.7,.15,.1,.05])[0]):
                if rng.random()<.3:
                    i,j=rng.sample(range(6),2);key[i],key[j]=key[j],key[i]
                else:key[6+rng.randrange(6)]=rng.randrange(6)
            key=tuple(key)
        if key in scores:continue
        search.WORD=makeword(key)
        rr=[]
        for seed in range(3):
            rules,root=search.repaire(seed,0 if seed else .5)
            rr.append((len(rules),rules,root))
        size,rules,root=min(rr,key=lambda t:t[0]);scores[key]=size
        if len(pool)<100 or size<pool[-1][0]:
            pool.append((size,key));pool.sort();pool=pool[:100]
        if size<best:
            best=size
            data={'nodes':size,'root':root,'rules':rules,'tokens':search.TOKENS,
                  'word':search.WORD,'head_permutation':[i+1 for i in key[:6]],
                  'parameter_permutations':[list(PERMS[i]) for i in key[6:]],'key':key}
            Path(__file__).with_name('variant_best.json').write_text(json.dumps(data,indent=2))
            print('best',size,'trial',trial,'key',key,'secs',round(time.time()-start,3),flush=True)
        if trial%10000==0:print('progress',trial,len(scores),best,flush=True)
    print('done',best,'trials',len(scores),'secs',round(time.time()-start,3),flush=True)
