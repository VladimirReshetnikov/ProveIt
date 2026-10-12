"""Paired complete graph-query measurements; no knot-recognition timing claim."""
import gc
import json
import math
import platform
import random
import statistics
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'experiments')]
from pattern_kernel.core import Block,expand,certify_cubic_graph,chain_payload
from pattern_kernel.verify import _check_graph
from routed_patterns import build_kernel,solve,verify_result
from routing_families import star_triangle,routed_edges,permutation_cycles


def timed(function):
    begin=time.perf_counter();result=function();return time.perf_counter()-begin,result


def direct_query(chain):
    graph,_=expand(chain,max_copies=20000)
    proof=certify_cubic_graph(graph)
    _check_graph(graph,proof)
    return proof['verdict']


def routed_query(chain):
    proof=solve(chain)
    assert verify_result(chain,proof)
    return proof['graph_proof']['verdict']


def main():
    rng=random.Random(20261012);rows=[]
    for n in [1,3,9,33,129,513,2049,8193]:
        chain=(Block(star_triangle(),n),)
        direct_query(chain);routed_query(chain)
        old=[];new=[]
        for _ in range(7):
            order=['direct','routed'];rng.shuffle(order)
            values={}
            for name in order:
                gc.collect()
                elapsed,verdict=timed(lambda:direct_query(chain) if name=='direct'
                                     else routed_query(chain))
                values[name]=verdict
                (old if name=='direct' else new).append(elapsed)
            assert values['direct']==values['routed']
        kernel,_,_=build_kernel(chain)
        rows.append({'copies':n,'source_bits':n.bit_length(),
                     'original_vertices':4*n,'original_edges':6*n,
                     'kernel_vertices':kernel.n,'kernel_edges':len(kernel.edges),
                     'explicit_median_seconds':statistics.median(old),
                     'routed_median_seconds':statistics.median(new),
                     'ratio_explicit_over_routed':statistics.median(old)/statistics.median(new),
                     'paired_ratio_median':statistics.median(a/b for a,b in zip(old,new)),
                     'paired_ratio_samples':[a/b for a,b in zip(old,new)],
                     'explicit_samples':old,'routed_samples':new})
    huge=[]
    for bits in [65,257,1025,4097,16385]:
        chain=(Block(star_triangle(),2**(bits-1)+1),)
        times=[];proof=None
        for _ in range(7):
            elapsed,_=timed(lambda:routed_query(chain));times.append(elapsed)
        proof=solve(chain)
        huge.append({'exponent_bits':bits,'kernel_edges':len(proof['kernel']['edges']),
                     'source_json_bytes':len(json.dumps(chain_payload(chain)).encode()),
                     'certificate_json_bytes':len(json.dumps(proof).encode()),
                     'median_seconds':statistics.median(times),'samples':times})
    lengths=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]
    permutation=permutation_cycles(lengths)
    tile=routed_edges(permutation)
    n=2**2048+12345
    elapsed,(kernel,plans,_)=timed(lambda:build_kernel((Block(tile,n),),close=False))
    period_example={'cycle_lengths':lengths,'width':len(permutation),
                    'global_period_decimal':str(math.lcm(*lengths)),
                    'global_period_bits':math.lcm(*lengths).bit_length(),
                    'exponent_bits':n.bit_length(),'kernel_vertices':kernel.n,
                    'kernel_edges':len(kernel.edges),'construction_seconds':elapsed,
                    'scope':'construction only; degree-two graph, no cubic terminal verdict'}
    control_chain=(Block(star_triangle(),129),)
    controls=[]
    for _ in range(7):
        order=['A','B'];rng.shuffle(order);sample={}
        for arm in order:
            gc.collect()
            sample[arm]=timed(lambda:direct_query(control_chain))[0]
        controls.append(sample)
    result={'python':platform.python_version(),'platform':platform.platform(),
            'timing_scope':'graph construction + exact query + proof replay; excludes parsing, serialization, embedding/ball validation, and knot recognition',
            'repeats':7,'shuffle_seed':20261012,'paired':rows,'binary':huge,
            'large_period_construction':period_example,
            'identical_explicit_control':{'copies':129,'samples':controls,
                'paired_ratio_median':statistics.median(x['A']/x['B'] for x in controls)}}
    (ROOT/'results/routing_benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'paired':[{k:v for k,v in x.items() if 'samples' not in k} for x in rows],
                      'binary':[{k:v for k,v in x.items() if k!='samples'} for x in huge],
                      'large_period':period_example},indent=2))


if __name__=='__main__':main()
