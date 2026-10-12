"""Paired end-to-end recognition with optional verified rank-two preprocessing.

Timed calls include Diagram construction, all default certificates, compression,
independent replay, and fallback. Imports are excluded. Allocation peaks are
measured separately with tracemalloc. No prior filters are disabled.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter
import tracemalloc

from fastunknot import Diagram, recognize


def sleeve(m,base):
    b=[base,-(base+1)]*m; z=[base,base+1,base]*2
    return b+z+[-v for v in b[::-1]]+[-v for v in z[::-1]]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--rounds',type=int,default=7)
    args=parser.parse_args();rng=random.Random(2026100811)
    cases=[(f'sleeve_{m}',dict(braid=dict(strands=4,word=sleeve(m,1)+sleeve(m,2)+[1,2,3])))
           for m in (1,16,64)]
    left=[1,2,3,1,2,1];right=[3,2,1,3,2,3]
    cases.append(('barrier_8',dict(braid=dict(strands=4,word=(left+[-v for v in right[::-1]])*8+[1,2,3]))))
    cases.append(('cheap_braid',dict(braid=dict(strands=4,word=[1,2,3]*7))))
    for name in ('stress_braid5_36','conway','kinoshita_terasaka'):
        cases.append((name,json.loads((Path(__file__).parent/'examples'/(name+'.json')).read_text())))
    rows=[]
    for name,data in cases:
        samples=[];results={}
        def run(arm):
            return recognize(Diagram.from_json(data),use_ranktwo=arm=='enabled',
                             ranktwo_seconds=.1,seconds=5)
        for _ in range(args.rounds):
            order=['baseline','control','enabled'];rng.shuffle(order);times={}
            for arm in order:
                start=perf_counter();result=run(arm);times[arm]=perf_counter()-start
                results[arm]=result.to_json()
            assert len({r['status'] for r in results.values()})==1
            assert results['baseline']['status']!='UNKNOWN'
            samples.append(dict(order=order,seconds=times))
        peaks={}
        for arm in ('baseline','enabled'):
            tracemalloc.start();measured=run(arm);_,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
            peaks[arm]=dict(bytes=peak,status=measured.status,method=measured.method)
        ratio=statistics.median(r['seconds']['baseline']/r['seconds']['enabled'] for r in samples)
        aa=statistics.median(r['seconds']['baseline']/r['seconds']['control'] for r in samples)
        rows.append(dict(name=name,input=data,samples=samples,results=results,peak_bytes=peaks,
                         median_speedup=ratio,median_aa=aa))
        print(name,round(ratio,3),round(aa,3),results['baseline']['method'],results['enabled']['method'],flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(),seed=2026100811,
        rounds=args.rounds,scope=__doc__,cases=rows),indent=2)+'\n')


if __name__=='__main__':main()
