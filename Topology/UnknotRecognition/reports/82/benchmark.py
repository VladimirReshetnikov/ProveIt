#!/usr/bin/env python3
"""Paired encoded-input surface-gluing measurements; no knot timing claims."""
from __future__ import annotations
import argparse
import gc
import json
import platform
import random
import statistics
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'tests')]
from corner_kernel import *
from corner_kernel.compiler import Port,compile_boundary
from corner_kernel.oracles import BlockOracle,SingletonOracle
from reference import literal_glue


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',default=str(ROOT/'data/benchmark.json'))
    parser.add_argument('--rounds',type=int,default=7)
    args=parser.parse_args()
    if args.rounds<1: raise ValueError('at least one round is required')
    rng=random.Random(61301012)
    result={'description':'same encoded surfaces; construct and classify one complete gluing',
            'python':sys.version,'platform':platform.platform(),'seed':61301012,
            'rounds':args.rounds,'warmup_rounds':1,'batching':'128 kernel queries; max(1,4096/physical_edges) literal queries; per-query means', 'cases':[],'huge_compiler':[]}
    for length in (1,4,16,64,256,1024,4096):
        surfaces=[Surface(1,1),Surface(1,1)]
        raw=[]
        for sid in range(2):
            word=[]
            for j in range(8):
                word.extend([Edge(f'{sid}:{j}'),Edge(length=length)])
            raw.append((sid,word))
        gs=[Gluing(f'0:{j}',f'1:{(3*j)%8}',1) for j in range(8)]
        expected=literal_glue(surfaces,raw,gs)
        def compact():return signature(glue(make_kernel(surfaces,raw),gs).kernel)
        def literal():return literal_glue(surfaces,raw,gs)
        funcs={'kernel':compact,'literal':literal,'literal_control':literal}
        repetitions={'kernel':128,'literal':max(1,4096//(16*(length+1))),
                     'literal_control':max(1,4096//(16*(length+1)))}
        samples=[]
        warmup=None
        for r in range(-1,args.rounds):
            order=list(funcs);rng.shuffle(order)
            record={'round':r,'order':order}
            for name in order:
                gc.collect()
                t=time.perf_counter_ns()
                for _ in range(repetitions[name]):
                    got=funcs[name]()
                    if got!=expected:raise AssertionError((name,length,got,expected))
                elapsed=time.perf_counter_ns()-t
                record[name]=elapsed/repetitions[name]
            if r>=0:samples.append(record)
            else:warmup=record
        ratio=statistics.median(x['literal']/x['kernel'] for x in samples)
        control=statistics.median(x['literal']/x['literal_control'] for x in samples)
        result['cases'].append({'gap_length':length,'physical_boundary_edges':16*(length+1),
             'kernel_edges':32,'signature':expected,'repetitions_per_arm':repetitions,'samples_ns':samples,'warmup_ns':warmup,
             'kernel_median_ms':statistics.median(x['kernel'] for x in samples)/1e6,
             'literal_median_ms':statistics.median(x['literal'] for x in samples)/1e6,
             'paired_ratio':ratio,'aa_control_ratio':control})
    for bits in (64,1024,4096,16384):
        p,L=12,1<<bits
        blocks=[(i*(L+1),(i+1)*(L+1)) for i in range(p)]
        rc=BlockOracle(blocks);vc=SingletonOracle(rc.n)
        ports=[Port(f'p{i:02}',0,blocks[(i-1)%p][1]-1,blocks[i][0]) for i in range(p)]
        times=[]
        warmup_time=None
        for r in range(-1,args.rounds):
            t=time.perf_counter_ns()
            for _ in range(32):
                k,m=compile_boundary([Surface(1,1)],ports,vc,rc)
            ns=(time.perf_counter_ns()-t)/32
            if r>=0:times.append(ns)
            else:warmup_time=ns
        result['huge_compiler'].append({'gap_length_bits':bits+1,
            'universe_bits':rc.n.bit_length(),'ports':p,'kernel_edges':sum(len(c.edges) for c in k.cycles),
            'orbit_count_calls':m.queries,'maximum_extra_pairings':m.maximum_extra_pairings,
            'median_ms':statistics.median(times)/1e6,'samples_ns':times,'warmup_ns':warmup_time,'repetitions_per_sample':32,
            'oracle':'analytic consecutive-block partition; not general AHT'})
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    for row in result['cases']:
        print(row['gap_length'],round(row['kernel_median_ms'],3),round(row['literal_median_ms'],3),round(row['paired_ratio'],3),round(row['aa_control_ratio'],3))
    for row in result['huge_compiler']: print('huge',row)

if __name__=='__main__':main()
