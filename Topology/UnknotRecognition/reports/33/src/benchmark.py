"""Paired kernel timings, not full fastunknot recognition benchmarks.

Compares the old birth-front normal form (without optional inverse pruning)
with commuting layers. Both use the same immutable transition kernel. All
traces through the depth bound are exhausted; goal tests do not stop the run.
Thus this measures duplicate-interleaving work, not an end-to-end speedup.
"""
from __future__ import annotations
from pathlib import Path
import argparse,json,platform,random,statistics,time
from layered_search import layered_traces,Stats
from abstract_models import BooleanSystem,Rule
from dart_kernel import from_braid,R3System

ROOT=Path(__file__).resolve().parents[1]

def birth_front_traces(system,initial,depth,max_roots):
    def children(state,active,births,phase,last,remaining):
        actions=sorted(system.actions(state),key=lambda a:a.key)
        if phase and births<max_roots:
            for a in actions:
                if (last is None or last<a.key) and active.isdisjoint(a.footprint):
                    yield a,births+1,True,a.key
        for a in actions:
            if not active.isdisjoint(a.footprint): yield a,births,False,last
    if not depth:return
    stack=[(initial,frozenset(),depth,children(initial,frozenset(),0,True,None,depth))]
    while stack:
        state,active,remaining,it=stack[-1]
        item=next(it,None)
        if item is None:stack.pop();continue
        a,b,p,last=item;y=system.apply(state,a);S=active|a.footprint
        yield y
        if remaining>1:stack.append((y,S,remaining-1,children(y,S,b,p,last,remaining-1)))

def run_benchmark(rounds=5):
    cases=[]
    for m,k in [(6,1),(6,6),(6,8)]:
        cases.append((f"independent_bits_{m}_k{k}",BooleanSystem([Rule(1<<i,0,0) for i in range(m)]),0,k,k,"abstract"))
    for q,k in [(4,1),(4,4),(7,4),(10,4)]:
        cases.append((f"torus_3_{q}_k{k}",R3System(),from_braid(3,[1,2]*q),k,k,"knot RIII"))
    rng=random.Random(8102602);rows=[]
    for name,sys,state,k,b,scope in cases:
        def old(): return sum(1 for _ in birth_front_traces(sys,state,k,b))
        def new(): return sum(1 for _ in layered_traces(sys,state,k,max_roots=b))
        expected={"birth_front":old(),"layered":new()};samples=[]
        for _ in range(rounds):
            arms=["birth_front","layered","control"];rng.shuffle(arms);times={};counts={}
            for arm in arms:
                fn=new if arm=="layered" else old
                t=time.perf_counter();cnt=fn();times[arm]=time.perf_counter()-t;counts[arm]=cnt
                assert cnt==expected["layered" if arm=="layered" else "birth_front"]
            samples.append(dict(order=arms,seconds=times,counts=counts))
        row=dict(name=name,scope=scope,depth=k,max_roots=b,trace_counts=expected,samples=samples,
             median_seconds={a:statistics.median(s["seconds"][a] for s in samples) for a in arms},
             paired_speedup=statistics.median(s["seconds"]["birth_front"]/s["seconds"]["layered"] for s in samples),
             control_ratio=statistics.median(s["seconds"]["birth_front"]/s["seconds"]["control"] for s in samples))
        rows.append(row);print(name,expected,"speedup",row["paired_speedup"],flush=True)
    result=dict(python=platform.python_version(),platform=platform.platform(),seed=8102602,
                rounds=rounds,scope=__doc__,rows=rows)
    (ROOT/"data"/"benchmark.json").write_text(json.dumps(result,indent=2)+"\n")
    return result
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--rounds",type=int,default=5);args=p.parse_args()
    if args.rounds<1:p.error("positive rounds required")
    run_benchmark(args.rounds)
