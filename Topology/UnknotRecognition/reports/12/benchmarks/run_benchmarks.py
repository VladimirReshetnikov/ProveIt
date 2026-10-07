"""Deterministic, paired arithmetic and raw-scanner benchmarks.

The scanner fixture retains the executable algorithm inspected in the current
repository; it is source-derived, not a byte-identical checkout. The legacy
archive is an independent correctness oracle, not the timing baseline.
"""
from __future__ import annotations
import argparse, csv, gc, json, os, pathlib, platform, random, statistics, sys, time
from datetime import datetime, timezone
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT),str(ROOT/'tests')]
from reference.upstream.planar import Planar
from unknot_frobenius.adapters import accelerated_planar_class
from unknot_frobenius.blocks import *
from test_upstream import run_scan
from reference.legacy.fastunknot.diagram import Diagram

FAST=accelerated_planar_class(Planar)

def measure(fn):
    gc.collect();enabled=gc.isenabled();gc.disable()
    start=time.perf_counter_ns()
    try: answer=fn()
    finally:
        elapsed=(time.perf_counter_ns()-start)/1e9
        if enabled: gc.enable()
    return answer,elapsed

def micro(repeats):
    rng=random.Random(2026100701);rows=[]
    for kind in ['dense','near_equal','sparse']:
        for b in [4,6,8,10]:
            for rep in range(repeats):
                if kind=='sparse':
                    fs=rng.sample(range(1<<b),3);gs=rng.sample(range(1<<b),3)
                    f=sum(1<<s for s in fs);g=sum(1<<s for s in gs)
                else:
                    f=rng.getrandbits(1<<b)
                    g=(f^(1<<rng.randrange(1<<b))) if kind=='near_equal' else rng.getrandbits(1<<b)
                if f==g or not f or not g: raise AssertionError('degenerate sample')
                engines={};ids={}
                for name,cls in [('baseline',Planar),('adaptive',FAST)]:
                    alg=cls(shape_cache=False);a=alg.intern(tuple((2*i,2*i+1) for i in range(b)))
                    alg.compose_plan(a,a,a)  # topology compilation excluded for both
                    engines[name]=alg;ids[name]=a
                for cache_state in ['cold','warm']:
                    outcomes={}
                    order=['baseline','adaptive'] if rep%2==0 else ['adaptive','baseline']
                    for name in order:
                        alg=engines[name];a=ids[name]
                        ans,elapsed=measure(lambda:alg.compose(a,a,a,f,g))
                        outcomes[name]=ans
                        rows.append(dict(kind=kind,variables=b,repetition=rep,cache=cache_state,
                                         engine=name,seconds=elapsed,left_support=f.bit_count(),
                                         right_support=g.bit_count(),difference_support=(f^g).bit_count(),
                                         memo_entries=len(alg.compose_plan(a,a,a)[1]),
                                         factored_calls=getattr(alg,'kernel_stats',{}).get('factored_calls',0)))
                    assert outcomes['baseline']==outcomes['adaptive']
    return rows

def scans(repeats):
    rows=[]
    cases={}
    for name in ['trefoil','figure_eight','hard_unknot_8','conway','kinoshita_terasaka','torus_3_5','unknot_braid40']:
        cases[name]=Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text())).pd
    cases['alternating_3_braid_10']=Diagram.from_braid(3,[1,-2]*5).pd
    for name,pd in cases.items():
        for rep in range(repeats):
            outcomes={}
            order=['baseline','adaptive'] if rep%2==0 else ['adaptive','baseline']
            for engine in order:
                try:
                    (answer,stats,kstats),elapsed=measure(lambda:run_scan(pd,accelerated=engine=='adaptive',seconds=15))
                    outcomes[engine]=answer
                    rows.append(dict(case=name,crossings=len(pd),repetition=rep,engine=engine,seconds=elapsed,
                                     rank=sum(answer.values()),status='completed',stats=stats,kernel_stats=kstats,
                                     by_degree=answer))
                except (RuntimeError,MemoryError) as exc:
                    rows.append(dict(case=name,crossings=len(pd),repetition=rep,engine=engine,status='resource_limit',reason=str(exc)))
            if len(outcomes)==2: assert outcomes['baseline']==outcomes['adaptive']
    return rows

def interfaces(repeats):
    rng=random.Random(772011);rows=[]
    b=3;r=2;p=q=2
    for n in [8,16,24]:
        for rep in range(repeats):
            u=matrix([[rng.getrandbits(1<<b)&~1 for _ in range(r)] for _ in range(n)])
            v=matrix([[rng.getrandbits(1<<b) for _ in range(n)] for _ in range(r)])
            c=matrix([[rng.getrandbits(1<<b) for _ in range(q)] for _ in range(n)])
            d=matrix([[rng.getrandbits(1<<b) for _ in range(n)] for _ in range(p)])
            e=matrix([[rng.getrandbits(1<<b) for _ in range(q)] for _ in range(p)])
            a=add(identity(n),mul(u,v,b))  # the full A is supplied to the full method
            timings={}
            if rep%2==0:
                full,timings['full_schur']=measure(lambda:schur(a,c,d,e,b))
            data,timings['build_interface']=measure(lambda:low_rank_interface(identity(n),u,v,c,d,e,b))
            small,timings['evaluate_interface']=measure(lambda:data.evaluate(b))
            if rep%2:
                full,timings['full_schur']=measure(lambda:schur(a,c,d,e,b))
            assert full==small
            rows.append(dict(size=n,interface_rank=r,variables=b,repetition=rep,**timings))
    return rows

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repeats',type=int,default=5);args=ap.parse_args()
    if args.repeats<1: ap.error('repeats must be positive')
    metadata=dict(utc=datetime.now(timezone.utc).isoformat(),python=sys.version,platform=platform.platform(),
                  processor=platform.processor(),cpu_count=os.cpu_count(),repeats=args.repeats,
                  baseline='Source-derived current Planar/FastScan execution fixture; see reference/README.md',
                  protocol='Fixed inputs and order; alternating paired order; garbage collection outside timed regions; topology precompiled in microbenchmarks; result equality asserted.')
    for name,fn in [('micro',micro),('scans',scans),('interfaces',interfaces)]:
        records=fn(args.repeats)
        (ROOT/'results'/f'{name}.json').write_text(json.dumps(dict(metadata=metadata,records=records),indent=2)+'\n')
        keys=list(dict.fromkeys(k for row in records for k in row))
        with (ROOT/'results'/f'{name}.csv').open('w',newline='') as fh:
            writer=csv.DictWriter(fh,fieldnames=keys);writer.writeheader()
            writer.writerows({k:json.dumps(v,sort_keys=True) if isinstance(v,dict) else v for k,v in row.items()} for row in records)
        print(name,len(records),flush=True)

if __name__=='__main__':main()
