#!/usr/bin/env python3
"""Same-input baseline/antipodal/projective microbenchmarks in existing rings."""
from __future__ import annotations
from dataclasses import asdict
import argparse
import csv
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
from baseline_packet_extraction import RingSpec,coefficient_reference,coefficient_finite_difference
from streamed_coefficients import coefficient_antipodal_gray
from projective_coefficients import coefficient_projective_12


def run(repetitions):
    rng=random.Random(202610263)
    specs=[("paired-quadratic",(2,)*q,32,RingSpec((1,1,1))) for q in (3,6,9)]
    specs += [
       ("paired-nilpotent",(2,)*6,48,RingSpec((1,1,1),2)),
       ("one-odd",(1,)+(2,)*6,32,RingSpec((1,1,1))),
       ("mixed",(1,1,2,2,2,2),32,RingSpec((1,1,1))),
       ("mixed-nilpotent",(1,1,2,2,2,2),48,RingSpec((1,1,1),2)),
       ("paired-low-precision",(2,)*6,1,RingSpec((1,1,1))),
       ("paired-high-precision",(2,)*6,256,RingSpec((1,1,1))),
       ("squarefree-control",(1,)*10,32,RingSpec((1,1,1))),
    ]
    methods=[("baseline",coefficient_finite_difference),
             ("antipodal_gray",coefficient_antipodal_gray),
             ("projective",coefficient_projective_12)]
    rows=[]
    for family,b,p,ring in specs:
        R=sum(b)
        forms=[tuple(tuple(rng.randrange(1<<p) for _ in range(ring.dimension))
                     for _ in b) for _ in range(R)]
        expected=coefficient_reference(forms,b[1:],p,ring)
        timings={name:[] for name,_ in methods}
        observations={}
        for repetition in range(repetitions):
            ordered=methods[repetition%3:]+methods[:repetition%3]
            for name,method in ordered:
                start=time.perf_counter()
                result=method(forms,b[1:],p,ring)
                seconds=time.perf_counter()-start
                if result.coefficient != expected:
                    raise AssertionError((family,name,"coefficient mismatch"))
                timings[name].append(seconds)
                observations[name]=asdict(result)
        medians={name:statistics.median(values) for name,values in timings.items()}
        row={"family":family,"R":R,"homogenized_b":list(b),"p":p,"ring":asdict(ring),
             "seconds":timings,"median_seconds":medians,
             "speedup_over_baseline":medians["baseline"]/medians["projective"],
             "speedup_over_antipodal":medians["antipodal_gray"]/medians["projective"],
             "observations":observations}
        rows.append(row)
        print(json.dumps({k:row[k] for k in ("family","R","median_seconds",
            "speedup_over_baseline","speedup_over_antipodal")}),flush=True)
    return {"scope":"Coefficient extraction microkernel; not SAT solve times",
            "seed":202610263,"repetitions":repetitions,"python":sys.version,
            "platform":platform.platform(),"rows":rows}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--repetitions",type=int,default=3)
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"results/local_checks")
    args=parser.parse_args()
    data=run(args.repetitions)
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"projective_benchmarks.json").write_text(json.dumps(data,indent=2)+"\n")
    with (args.output/"projective_benchmark_summary.csv").open('w',newline='') as f:
        w=csv.writer(f)
        w.writerow(["family","R","p","ring_dimension","baseline_evaluations","antipodal_evaluations","projective_evaluations",
             "baseline_precision","antipodal_precision","projective_precision","baseline_seconds","antipodal_seconds","projective_seconds",
             "speedup_over_baseline","speedup_over_antipodal"])
        for x in data['rows']:
            obs=x['observations'];med=x['median_seconds']
            w.writerow([x['family'],x['R'],x['p'],(len(x['ring']['f'])-1)*x['ring']['ell'],
                *[obs[k]['evaluation_count'] for k in ('baseline','antipodal_gray','projective')],
                *[obs[k]['working_precision'] for k in ('baseline','antipodal_gray','projective')],
                *[med[k] for k in ('baseline','antipodal_gray','projective')],x['speedup_over_baseline'],x['speedup_over_antipodal']])
