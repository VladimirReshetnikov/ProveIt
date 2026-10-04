#!/usr/bin/env python3
"""Independent exhaustive small-input validation. No optional dependencies.
All one-component closed 3-braid words of lengths 2,4,6 over +/-sigma_1,+/-sigma_2.
Also records the large benchmark's determinant and alternative-scan consistency.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram, khovanov_rank, recognize, verify_rejection
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.jones import jones_evaluations
from fastunknot.scan import clear_caches
from fastunknot.simplify import simplify
from reference import one_component, brute_jones, reference_reduced_rank


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-length',type=int,default=6,choices=(2,4,6,8))
    parser.add_argument('--output',type=Path,default=ROOT/'results/exhaustive.json')
    parser.add_argument('--skip-large',action='store_true')
    args=parser.parse_args()
    start=time.perf_counter()
    histogram={};cases=[];digest=hashlib.sha256();certificates=0;unknots=0
    for n in range(2,args.max_length+1,2):
        count=0
        for word in itertools.product((-2,-1,1,2),repeat=n):
            if not one_component(3,word):continue
            d=Diagram.from_braid(3,word)
            clear_caches()
            rank=reference_reduced_rank(d)
            direct=khovanov_rank(d.pd,factor_connected=False,check_d_squared=True)
            factored=khovanov_rank(d.pd)
            assert rank==direct['reduced_rank']==factored['reduced_rank'],word
            assert direct['by_degree']==factored['by_degree'],word
            jones=brute_jones(d)
            assert jones_evaluations(d)['normalized']==jones,word
            result=recognize(d)
            assert result.status==('UNKNOT' if rank==1 else 'KNOTTED'),word
            if rank==1:
                assert jones==[1,1],word
                unknots+=1
            elif 'witness' in result.evidence:
                assert verify_rejection(d,result),word
                certificates+=1
            digest.update(json.dumps([word,rank,jones],separators=(',',':')).encode()+b'\n')
            count+=1
            histogram[rank]=histogram.get(rank,0)+1
        cases.append({'crossings':n,'one_component_words':count})
        print(n,count,'elapsed',round(time.perf_counter()-start,2),flush=True)
    report={'python':sys.version,'cases':cases,'rank_histogram':histogram,
            'total':sum(x['one_component_words'] for x in cases),'unknot_words':unknots,
            'rejection_certificates_verified':certificates,'mismatches':0,
            'result_stream_sha256':digest.hexdigest(),'exhaustive_seconds':time.perf_counter()-start,
            'oracles':'direct enhanced-state cube differential; independent full Kauffman state sum'}
    if not args.skip_large:
        d=Diagram.from_json(json.loads((ROOT/'fast/examples/random_5_braid_36.json').read_text()))
        p=alexander_polynomial(d)
        full=khovanov_rank(d.pd,factor_connected=False)
        reduced,moves=simplify(d)
        r=khovanov_rank(reduced.pd,check_d_squared=True)
        # Rank is R1/R2 invariant, unlike the unshifted degree histogram.
        assert full['reduced_rank']==r['reduced_rank']==2949
        # Full baseline geometry with LIFO is checked separately by the benchmark.
        # The determinant agreement is independent evidence, not an independent
        # complete-rank proof for this 36-crossing input.
        report['large_consistency']={'original_crossings':d.crossings,'simplified_crossings':reduced.crossings,
            'moves':[m.to_json() for m in moves],'reduced_rank':full['reduced_rank'],
            'simplified_reduced_rank':r['reduced_rank'],'simplified_d_squared_checked':True,
            'alexander_coefficients':p,'determinant':abs(evaluate(p,-1)),
            'independent_dense_rank_checked':False}
    report['total_seconds']=time.perf_counter()-start
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
