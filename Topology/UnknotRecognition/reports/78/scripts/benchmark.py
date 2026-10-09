#!/usr/bin/env python3
"""Paired exact-query benchmarks; neither method is a native knot recognizer."""
import sys, time, json, statistics, platform
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from span_excess import *
from span_excess.prepare import prepare_model


def model(L):
    return prepare_model(4,[(0,1,2,3)]*2,[(0,0,0,0),(L,0,0,0)],
                         [(0,1,-L//3,2),(1,2,1,1),(2,3,-2,2)])


def exhaustive(m,k):
    # Normalize p0=0. For every j, D >= |pj|+|L-pj|.
    # Hence every feasible integer lies in [-floor(k/2), L+floor(k/2)].
    a,b=-(k//2),m.optimum+k//2
    best={};count=0
    for tail in product(range(a,b+1),repeat=3):
        p=(0,)+tail;count+=1;q=m.span(p)-m.optimum
        if q<=k:
            score=m.score2(p);best[q]=max(best.get(q,score),score)
    return best,count


def timed(fn):
    t=time.perf_counter();ans=fn();return ans,time.perf_counter()-t


def main():
    output={'python':platform.python_version(),'platform':platform.platform(),
            'query':'entire exact-span Euler-score profile for the two-tetrahedron abstract family',
            'excluded':'minimum-span preparation is excluded equally from both timings',
            'warning':'algebraic benchmarks, not native recognition timings; exhaustive baseline is not claimed best possible',
            'paired':[],'binary':[]}
    for L in (2,4,8,16,32,64):
        m=model(L);k=2;samples=[]
        for r in range(5):
            if r%2:
                a,ta=timed(lambda:optimize_band(m,k,save_cells=False))
                b,tb=timed(lambda:exhaustive(m,k))
            else:
                b,tb=timed(lambda:exhaustive(m,k))
                a,ta=timed(lambda:optimize_band(m,k,save_cells=False))
            assert {int(q):row['score2'] for q,row in a['profile'].items()}==b[0]
            samples.append({'stratified_seconds':ta,'exhaustive_seconds':tb})
        sm=statistics.median(x['stratified_seconds'] for x in samples)
        bm=statistics.median(x['exhaustive_seconds'] for x in samples)
        output['paired'].append({'L':L,'radius':k,'candidate_potentials':b[1],
            'strata':a['stats']['strata'],'feasible_strata':a['stats']['feasible_strata'],
            'stratified_median_seconds':sm,'exhaustive_median_seconds':bm,
            'exhaustive_over_stratified':bm/sm,'samples':samples})
    for bits in (16,64,256,1024,4096,16384):
        m=model(1<<bits)
        samples=[]
        for r in range(3):
            a,t=timed(lambda:optimize_band(m,2,save_cells=False));samples.append(t)
        output['binary'].append({'height_exponent':bits,'strata':a['stats']['strata'],
                                 'work':a['stats']['work'],'augmentations':a['stats']['augmentations'],
                                 'median_seconds':statistics.median(samples),'samples':samples})
    (ROOT/'results/benchmark.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()
