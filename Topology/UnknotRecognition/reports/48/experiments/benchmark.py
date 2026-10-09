"""Paired timings from the SAME SLP input; no full-pipeline speed claim."""
import argparse
import json
from pathlib import Path
import platform
from statistics import median
import sys
from time import perf_counter
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from compressed_b3 import recognize,verify
from compressed_b3.grammar import expand,validate
from experiments.families import sleeve
from experiments.oracles import explicit


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds',type=int,default=7)
    parser.add_argument('--output',type=Path,default=ROOT/'results/benchmark.json')
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    rows=[]
    for k in (0,4,8,10,12,14,16,18):
        data=sleeve(k)
        def compressed():
            out=recognize(data)
            return verify(data,out['certificate'])
        def expanded():
            return explicit(expand(data,limit=1100000))
        assert compressed()==expanded()=='UNKNOT'
        samples={'compressed_and_replay':[],'expand_and_stack':[]}
        methods=[('compressed_and_replay',compressed),('expand_and_stack',expanded)]
        for round_index in range(args.rounds):
            for name,fn in methods[::1 if round_index%2==0 else -1]:
                start=perf_counter();status=fn();elapsed=perf_counter()-start
                assert status=='UNKNOT'
                samples[name].append(elapsed)
        med={name:median(values) for name,values in samples.items()}
        row=dict(k=k,input_rules=len(data['rules'])-1,
                 expanded_crossings=validate(data).lengths[data['root']],
                 raw_seconds=samples,median_seconds=med,
                 baseline_over_compressed=med['expand_and_stack']/med['compressed_and_replay'])
        rows.append(row)
        print(k,row['expanded_crossings'],{n:round(v*1000,3) for n,v in med.items()},round(row['baseline_over_compressed'],2),flush=True)
    result=dict(python=sys.version,platform=platform.platform(),rounds=args.rounds,
        scope='Same native binary SLP input. New discovery plus independent certificate replay versus expansion plus source-derived explicit three-braid stack control. Not production fastunknot, not a knot corpus comparison, not an explicit-input speedup claim.',
        timing_inclusions='Input grammar is constructed outside both timed paths; validation and in-memory certificate construction/replay included; JSON disk I/O excluded.',
        ordering='alternating AB/BA after one untimed warmup of each method',rows=rows)
    args.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
