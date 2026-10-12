"""Isolated endpoint-remapping scaling; no claim of whole-knot speedup."""
import argparse
import json
from pathlib import Path
import random
import statistics
import sys
import time


def naive(rows,gaps):
    def shifted(point):
        return point-sum(hi-lo+1 for lo,hi in gaps if hi<point)
    return [[shifted(a),shifted(b),shifted(c),shifted(d),sign]
            for a,b,c,d,sign in rows],sum(hi-lo+1 for lo,hi in gaps)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=5)
    args=p.parse_args()
    sys.path.insert(0,str(args.repo/'Topology/UnknotRecognition/fast'))
    from fastunknot.interval_orbit_verify import _contract_pairings
    rng=random.Random(20261012);result=dict(rounds=args.rounds,seed=20261012,scope='endpoint remapping only',cases=[])
    for k in (64,128,256,512,1024,2048,4096):
        gaps=[[4*i+1,4*i+2] for i in range(k)]
        rows=[[4*i,4*i,4*i+3,4*i+3,-1] for i in range(k)]
        expected=([[2*i,2*i,2*i+1,2*i+1,-1] for i in range(k)],2*k)
        samples=[]
        for repetition in range(args.rounds):
            order=['naive','prefix'];rng.shuffle(order);sample=dict(order=order)
            for name in order:
                start=time.perf_counter_ns()
                value=(naive if name=='naive' else _contract_pairings)(rows,gaps)
                sample[name]=(time.perf_counter_ns()-start)/1e9
                assert value==expected
            samples.append(sample)
        record=dict(pairings=k,gaps=k,universe=4*k,exact_output_parity=True,samples=samples,
                    median_seconds={name:statistics.median(s[name] for s in samples) for name in ('naive','prefix')},
                    median_paired_ratio=statistics.median(s['naive']/s['prefix'] for s in samples))
        result['cases'].append(record)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k!='samples'}),flush=True)
