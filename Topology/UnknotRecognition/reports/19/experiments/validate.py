#!/usr/bin/env python3
"""Reproducible exhaustive/independent checks, separate from fast unit tests."""
import argparse
import itertools
import json
import platform
import random
import time
from pathlib import Path
from ranktwo import compress, optimal_pass, verify
from ranktwo.search_group import QuotientTrie
from ranktwo.verify import b3_central_form
from ranktwo.oracles import artin_action, brute_optimum, burau_minus_one
from ranktwo.cube import reduced_rank


def groups():
    trie=QuotientTrie(); seen={}; reverse={}; count=0
    for n in range(9):
        for word in itertools.product((1,-1,2,-2),repeat=n):
            node=0
            for g in word:node=trie.append_generator(node,g)
            e=sum(1 if g>0 else -1 for g in word)
            central,factors=b3_central_form(word)
            tokens=tuple(0 if family==0 else power for family,power in factors)
            assert trie.tokens(node)==tokens
            assert e==6*central+sum(3 if family==0 else 2*power for family,power in factors)
            key=(node,e); independent=burau_minus_one(word)
            assert key not in seen or seen[key]==independent
            assert independent not in reverse or reverse[independent]==key
            seen[key]=independent; reverse[independent]=key; count+=1
    return {'word_count':count,'maximum_length':8,'distinct_group_keys':len(seen),
            'quotient_nodes':len(trie.parent),'mismatches':0,
            'checks':'persistent quotient/exponent vs central normal form and Burau/exponent'}


def optimality():
    counts={}; instances=0
    for s,max_n in ((3,7),(4,5)):
        letters=tuple(g for i in range(1,s) for g in (i,-i)); count=0
        for n in range(max_n+1):
            for word in itertools.product(letters,repeat=n):
                for radius in (0,1):
                    a,plan,stats=optimal_pass(s,word,radius=radius,dictionary='avl')
                    b,other,_=optimal_pass(s,word,radius=radius,dictionary='hash')
                    assert a==b and plan==other
                    assert n-len(a)==brute_optimum(s,word,radius)
                    assert stats['group_advances']<=2*n
                    assert stats['maximum_active_corridors']<=2
                    instances+=1
                count+=1
        counts[f'B{s}_words_through_{max_n}']=count
    return {**counts,'radius_instances':instances,'dictionary_runs':2*instances,'mismatches':0}


def independent():
    rng=random.Random(20261007); count=0; removed=introduced=0
    for _ in range(1000):
        s=rng.randrange(2,9); n=rng.randrange(0,31)
        letters=tuple(g for i in range(1,s) for g in (i,-i))
        word=tuple(rng.choice(letters) for _ in range(n))
        result=compress(s,word); output,replay=verify(s,word,result['certificate'])
        assert artin_action(s,word)==artin_action(s,output)
        assert replay['removed_nodes']<=3*n//2
        removed+=replay['removed_nodes']; introduced+=replay['introduced_nodes'];count+=1
    homology=0
    for _ in range(100):
        s=rng.randrange(2,5); n=rng.randrange(0,9)
        letters=tuple(g for i in range(1,s) for g in (i,-i))
        word=tuple(rng.choice(letters) for _ in range(n))
        output=compress(s,word)['word']
        before=reduced_rank(s,word,check_square=True)
        after=reduced_rank(s,output,check_square=True)
        assert before['homology_rank']==after['homology_rank']
        homology+=1
    return {'seed':20261007,'Artin_action_cases':count,'Khovanov_invariance_cases':homology,
            'd_squared_zero_cubes':2*homology,'removed_nodes':removed,
            'introduced_nodes':introduced,'mismatches':0}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=('groups','optimality','independent'))
    parser.add_argument('--out',default='results');args=parser.parse_args()
    start=time.perf_counter();result=globals()[args.mode]()
    result.update(seconds=time.perf_counter()-start,python=platform.python_version(),
                  platform=platform.platform(),mode=args.mode)
    destination=Path(args.out);destination.mkdir(parents=True,exist_ok=True)
    (destination/f'validation_{args.mode}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
