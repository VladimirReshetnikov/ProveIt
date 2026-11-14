#!/usr/bin/env python3
"""Explore source-equivalent permutations of the six independent AX heads."""
import itertools,time,json,sys,random
from pathlib import Path
import search_grammar as search

ORIG=list(search.WORD)
BOUNDS=[18,35,54,70,86,102,121]
HEADS=[ORIG[a:b] for a,b in zip(BOUNDS,BOUNDS[1:])]
PREFIX=ORIG[:18];SUFFIX=ORIG[121:]
assert PREFIX+sum(HEADS,[])+SUFFIX==ORIG

if __name__=='__main__':
    start=time.time();best=1000
    trials=int(sys.argv[1]) if len(sys.argv)>1 else 20
    for perm in itertools.permutations(range(6)):
        search.WORD=PREFIX+sum((HEADS[i] for i in perm),[])+SUFFIX
        for seed in range(trials):
            rules,root=search.repaire(seed,0 if seed%2 else 1.5)
            size=len(rules)
            if size<best:
                best=size
                data={'nodes':size,'root':root,'rules':rules,'tokens':search.TOKENS,
                    'word':search.WORD,'head_permutation':[i+1 for i in perm]}
                Path(__file__).with_name('permuted_best.json').write_text(json.dumps(data,indent=2))
                print('best',size,'permutation',perm,'seed',seed,'secs',round(time.time()-start,3),flush=True)
    print('done',best,round(time.time()-start,3),flush=True)
