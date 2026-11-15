#!/usr/bin/env python3
"""Exhaust 4,104 specified loop trees, coefficients 4 through 9, returns 2/3.
Reports raw states minus a maximum disjoint raw-action matching.  A projected
score is not a physical/compiler proof.  Only the four released coefficient-4
tables are promoted, with their independent universal checks.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'construction'))
import build
from search_support import proposed_folds

@lru_cache(None)
def inc_trees(n):
    if n==1:return [build.INC]
    return [(a,b) for k in range(1,n) for a in inc_trees(k) for b in inc_trees(n-k)]

def main(out):
    raw,nodes,ax,sites,ins,parent=build.load_inputs();results=[];start=time.monotonic()
    for k in range(4,10):
        trees=[(a,('leaf','continueTo',2))for a in inc_trees(k)]
        trees += [(a,(b,('leaf','continueTo',3)))for j in range(1,k)for a in inc_trees(j)for b in inc_trees(k-j)]
        histogram={};minimum=999;source_equal=0
        for tree in trees:
            candidate=build.compile_loop(raw,tree);folds=proposed_folds(candidate)
            score=len(candidate)//2-len(folds);histogram[score]=histogram.get(score,0)+1;minimum=min(minimum,score)
            if k==4:
                nn=dict(nodes);nn['node62']=tree
                _,new=build.source(nn,ax);assert new==ins;source_equal+=1
        result=dict(coefficient=k,trees=len(trees),minimum_projected_states=minimum,histogram=histogram,
                    source_graph_identity_checks=source_equal)
        results.append(result);print(json.dumps(result),flush=True)
    assert sum(r['trees']for r in results)==4104
    assert [r['minimum_projected_states']for r in results]==[194,194,194,195,195,195]
    build.dump(out,dict(families=results,seconds=time.monotonic()-start,
                       scope='Only the enumerated return-2/return-3 loop family and raw-action matching score. No global lower bound.'))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,default=ROOT/'research/loop_enumeration_receipt.json')
    main(p.parse_args().out)
