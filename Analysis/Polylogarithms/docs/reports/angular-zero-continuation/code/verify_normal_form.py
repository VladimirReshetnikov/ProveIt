#!/usr/bin/env python3
"""Replay meaningful normal-form checks against the pinned original A_w."""
from pathlib import Path
import json,sys
from random import Random
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'upstream'))
from package_io import read_json
from full_ds import system
from kernel_normal_form import coordinates,normal_form,moments,kernel_vector

def verify():
    rng=Random(1729);results=[]
    for w in range(3,16,2):
        keys,A,rhs,labels=system(w)
        assert tuple(keys)==coordinates(w)
        for row in A.tolist():
            t={k:int(v) for k,v in zip(keys,row) if v}
            assert not normal_form(w,t)
            assert not moments(w,t)
        for _ in range(10):
            t={key:rng.randrange(-3,4) for key in keys}
            assert bool(normal_form(w,t))==bool(moments(w,t))
            for desc,expected in moments(w,t).items():
                v=kernel_vector(w,*desc)
                assert sum(c*v.get(key,0) for key,c in t.items())==expected
        record={'weight':w,'original_rows_checked':A.rows,'coordinates':A.cols,
                'deterministic_random_targets':10,'pass':True}
        results.append(record);print(record,flush=True)
    for w in range(2,13,2):
        keys,A,rhs,labels=system(w)
        assert A.rank()==A.cols
        ng=[i for i,k in enumerate(keys) if k[2:]!=(1,0)]
        assert A[:,ng].rank()==len(ng)
        record={'weight':w,'full_column_rank':A.cols,
                'full_column_rank_without_g':len(ng),'pass':True}
        results.append(record);print(record,flush=True)
    assert results == read_json('normal_form_receipt.json'), 'Normal-form reference receipt changed'
    return results

if __name__=='__main__':verify()
