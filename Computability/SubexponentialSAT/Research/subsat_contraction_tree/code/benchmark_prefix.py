#!/usr/bin/env python3
"""Paired, exact local-kernel benchmarks; no SAT runtime is measured.

The control evaluates the reviewed products separately in the same modular
ring as the new recurrence. Both methods include common prefactor generation,
return identical feature vectors, and are checked on every timed repeat.
"""
from __future__ import annotations
import argparse,csv,gc,json,platform,statistics,sys,time
from dataclasses import asdict
from pathlib import Path
sys.dont_write_bytecode=True
from cauchy_prefix import PrefixKernel, Work, collect

def run(repeats=3):
    rows=[]
    cases=[(4,1,8,128),(6,2,32,128),(8,3,128,128),
           (9,4,256,128),(10,5,512,128),(10,5,512,256)]
    for a,i,B,p in cases:
        N=1<<(a-1)
        ports=list(range(max(0,N-4),N))
        times={'prefix':[],'direct':[]}
        work={}
        expected=None
        for repeat in range(repeats):
            methods=('direct','prefix') if repeat%2==0 else ('prefix','direct')
            for method in methods:
                stats=Work()
                gc.collect()
                gc.disable()
                begin=time.perf_counter_ns()
                try:
                    kernel=PrefixKernel(a,i,1<<i,p,(0,1),stats)
                    features=collect(kernel,ports,B,method,True)
                finally:
                    elapsed=time.perf_counter_ns()-begin
                    gc.enable()
                if expected is None:expected=features
                elif expected!=features:raise RuntimeError('timed outputs differ')
                times[method].append(elapsed/1e9)
                work[method]=asdict(stats)
        d=statistics.median(times['direct']);f=statistics.median(times['prefix'])
        row={'a':a,'i':i,'precision':p,'packet_ports':N,'sampled_ports':len(ports),
             'retained_modes':B,'largest_weight':kernel.weight(B-1),
             'direct_median_seconds':d,'prefix_median_seconds':f,
             'speedup':d/f,'direct_multiplications':work['direct']['multiplications'],
             'prefix_multiplications':work['prefix']['multiplications'],
             'direct_unit_inversions':work['direct']['unit_inversions'],
             'prefix_unit_inversions':work['prefix']['unit_inversions'],
             'all_outputs_equal':True,'timings_seconds':times}
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='timings_seconds'}),flush=True)
    return {'scope':'Full-crossing Cauchy feature generation only; no full SAT solver.',
            'control':'Independently evaluated product formulas using identical modular arithmetic.',
            'platform':platform.platform(),'python':sys.version,'repeats':repeats,
            'includes_common_prefactor':True,'precomputation_cached_across_runs':False,
            'cases':rows}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('prefix_benchmark.json'))
    parser.add_argument('--csv',type=Path,default=Path('prefix_benchmark.csv'))
    parser.add_argument('--repeats',type=int,default=3)
    args=parser.parse_args()
    result=run(args.repeats)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    keys=[k for k in result['cases'][0] if k!='timings_seconds']
    with args.csv.open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=keys)
        writer.writeheader()
        writer.writerows({k:row[k] for k in keys} for row in result['cases'])
