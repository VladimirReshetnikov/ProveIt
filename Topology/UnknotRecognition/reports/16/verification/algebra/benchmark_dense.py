"""Paired cold-plan benchmarks for exact cobordism composition.

Run this script directly; bundle paths are resolved relative to this file.
Timings include geometric and coefficient plan construction but exclude
imports, algebra-object construction, input generation, and explicit gc.collect().
"""
from __future__ import annotations
import argparse
import gc
import json
import platform
import random
import statistics
import sys
from pathlib import Path
from time import perf_counter

from bundle_paths import HERE, baseline_module
from fastunknot.dense_compose import AdaptivePlanar


def one(m, f, g, mode):
    cls = baseline_module('planar').Planar if mode == 'baseline' else AdaptivePlanar
    alg = cls() if mode == 'baseline' else cls(force_dense=(mode == 'dense'))
    a = alg.intern(tuple((2*i, 2*i+1) for i in range(m)))
    gc.collect()
    start = perf_counter()
    result = alg.compose(a, a, a, f, g)
    seconds = perf_counter() - start
    memo = alg.compose_plans.get((a,a,a))
    return result, {'seconds':seconds, 'memo_entries':len(memo[1]) if memo else 0,
                    'dense_calls':getattr(alg,'dense_calls',0),
                    'sparse_calls':getattr(alg,'sparse_calls',0)}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--max-m',type=int,default=11)
    p.add_argument('--repeats',type=int,default=5)
    p.add_argument('--output',type=Path,default=HERE/'dense_benchmarks_reproduced.json')
    args=p.parse_args()
    if args.max_m < 4 or args.repeats < 1:
        p.error('--max-m must be at least 4 and --repeats must be positive')
    rng=random.Random(202610071)
    records=[]
    for m in range(4,args.max_m+1):
        f,g=rng.getrandbits(1<<m),rng.getrandbits(1<<m)
        samples={key:[] for key in ('baseline','adaptive','dense')}
        answer=None
        for repeat in range(args.repeats):
            modes=list(samples)
            rng.shuffle(modes)
            for mode in modes:
                value,data=one(m,f,g,mode)
                if answer is None: answer=value
                assert value==answer,(m,mode)
                samples[mode].append(data)
        med={key:statistics.median(x['seconds'] for x in vals) for key,vals in samples.items()}
        row={'arcs':m,'boundary_points':2*m,'basis_bits':1<<m,
             'left_terms':f.bit_count(),'right_terms':g.bit_count(),
             'median_seconds':med,'speedup_adaptive':med['baseline']/med['adaptive'],
             'speedup_dense':med['baseline']/med['dense'],'samples':samples}
        records.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='samples'}),flush=True)
        Path(args.output).write_text(json.dumps({'seed':202610071,'python':sys.version,
            'platform':platform.platform(),'paired_order':'seeded random',
            'timing_scope':'cold composition incl plan construction; excludes imports/input generation',
            'records':records},indent=2)+'\n')

if __name__=='__main__': main()
