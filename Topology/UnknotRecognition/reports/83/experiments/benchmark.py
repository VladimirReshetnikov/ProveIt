"""Paired complete GRAPH-query and certificate-replay benchmark; not knot timings."""
import gc
import json
import platform
import random
import statistics
import sys
import time
from pathlib import Path
from pattern_kernel import *
from pattern_kernel.core import certify_cubic_graph,validate_chain
from pattern_kernel.verify import _check_graph


def original(c):
    validate_chain(c)
    g,_=expand(c)
    proof=certify_cubic_graph(g)
    _check_graph(g,proof)
    return proof['verdict']


def compressed(c):
    proof=solve(c)
    assert verify_result(c,proof)
    return proof['graph_proof']['verdict']


def timed(fn,c):
    gc.collect()  # outside measured interval in both arms
    before=time.perf_counter_ns();result=fn(c);elapsed=time.perf_counter_ns()-before
    return elapsed/1e6,result


def main():
    rng=random.Random(41012);rows=[]
    for n in [1,3,4,8,16,32]:
        c=(Block(prism_tile(),n),)
        expected=original(c);assert compressed(c)==expected
        samples=[]
        for round_ in range(5):
            arms=[('explicit',original),('kernel',compressed)];rng.shuffle(arms);r={}
            for name,fn in arms:
                elapsed,value=timed(fn,c);assert value==expected;r[name+'_ms']=elapsed
            r['round']=round_;r['order']=[name for name,_ in arms]
            r['ratio']=r['explicit_ms']/r['kernel_ms'];samples.append(r)
        row={'copies':n,'verdict':expected,'samples':samples,
             'explicit_median_ms':statistics.median(s['explicit_ms'] for s in samples),
             'kernel_median_ms':statistics.median(s['kernel_ms'] for s in samples),
             'median_paired_ratio':statistics.median(s['ratio'] for s in samples)}
        rows.append(row);print(n,row['median_paired_ratio'],flush=True)
    # A/A scheduling control: same complete explicit implementation, no hidden cap.
    control=[];c=(Block(prism_tile(),16),)
    for i in range(5):
        a,_=timed(original,c);b,_=timed(original,c);control.append({'a_ms':a,'b_ms':b,'ratio':a/b})
    huge=[]
    for bits in [128,1024,4096,16384]:
        c=(Block(prism_tile(),2**bits+1),);compressed(c)
        samples=[timed(compressed,c)[0] for _ in range(5)]
        huge.append({'exponent':f'2^{bits}+1','bit_length':bits+1,
                     'kernel_median_ms':statistics.median(samples),'samples_ms':samples})
    out={'python':sys.version,'platform':platform.platform(),'seed':41012,
         'rounds':5,'warmups_per_case':1,'rows':rows,'identical_explicit_control':control,
         'control_median_ratio':statistics.median(x['ratio'] for x in control),
         'large_binary_cases':huge,'scope':'graph predicate plus proof production and replay',
         'excludes':['input parsing','proof serialization','geometry validation','knot recognition'],
         'native_recognizer_benchmark':'NOT_RUN'}
    p=Path(__file__).resolve().parent/'benchmark.json';p.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
