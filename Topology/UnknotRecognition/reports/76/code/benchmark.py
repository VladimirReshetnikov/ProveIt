"""Paired synthetic-grammar timings, including a narrower one-sided control.

These are not knot-recognition timings. All methods finish and their exact
optima are compared. Raw samples, source workloads, and counters are saved.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
import random
import statistics
import time
from pathlib import Path
from disk_algebra import partitions, identity, canonical
from compressed_search import repeated_source, solve, sequential
from sequential_baseline import run as one_sided


def cases():
    rng=random.Random(2026100923)
    libraries={}
    for b,q,m in ((2,2,12),(3,2,20),(4,1,24)):
        ps=list(partitions(2*b))
        opts=[{'partition':list(identity(b).partition),'cost':2,'charge':0},
              {'partition':list(identity(b).partition),'cost':1,'charge':q-1}]
        opts += [{'partition':list(rng.choice(ps)),'cost':rng.randrange(-4,8),'charge':rng.randrange(q)}
                 for _ in range(m-2)]
        libraries[(b,q)]=opts
    out=[]
    for b,q,w in ((2,2,2),(3,2,4),(4,1,4),(2,2,256),(3,2,256),
                  (2,2,4096),(3,2,512)):
        left=(0,)*b
        right=tuple(range(b))
        cap=canonical(left+tuple(1+x for x in right))
        out.append({'name':f'b{b}_q{q}_W{w}','width':b,'charges':q,'repetitions':w,
                    'options':libraries[(b,q)],'left_cap':left,'right_cap':right,'cap':cap,
                    'allowed_charges':[q-1]})
    return out


def run(repeats, names=None):
    result=[]
    for case in cases():
        if names is not None and case["name"] not in names:
            continue
        b,q,w=case['width'],case['charges'],case['repetitions']
        source=repeated_source(b,case['options'],w,q)
        cap=tuple(case['cap']);allowed=case['allowed_charges']
        def powered():
            r=solve(source);return r.query(cap,allowed)['cost'],r.metrics
        def scan():
            return one_sided(b,case['options'],w,case['left_cap'],case['right_cap'],allowed)
        def two_sided():
            from disk_algebra import disk_cap
            rows=sequential(source,w)
            vals=[x.cost for x in rows if x.charge in allowed and disk_cap(x.partition,cap)]
            return (min(vals) if vals else None),{'final_table':len(rows)}
        methods={'powered':powered,'one_sided_scan':scan,'two_sided_scan':two_sided}
        # Untimed warmup for each method, not just the proposed one.
        warm={key:f() for key,f in methods.items()}
        assert len({x[0] for x in warm.values()})==1
        samples={key:[] for key in methods}
        keys=list(methods)
        for trial in range(repeats):
            # Rotate execution order to reduce order bias.
            order=keys[trial%len(keys):]+keys[:trial%len(keys)]
            for key in order:
                start=time.perf_counter();value,metrics=methods[key]();elapsed=time.perf_counter()-start
                assert value==warm['powered'][0]
                samples[key].append(elapsed)
        med={k:statistics.median(v) for k,v in samples.items()}
        row={'workload':case,'optimum':warm['powered'][0],'raw_seconds':samples,'median_seconds':med,
             'speedup_vs_one_sided':med['one_sided_scan']/med['powered'],
             'speedup_vs_two_sided':med['two_sided_scan']/med['powered'],
             'work_counters':{k:v[1] for k,v in warm.items()}}
        result.append(row)
        print(case['name'],med,'ratios',row['speedup_vs_one_sided'],row['speedup_vs_two_sided'],flush=True)
    return {'status':'PASS','seed':2026100923,'repeats':repeats,
            'scope':'synthetic explicit finite patch grammars, not native knots',
            'environment':{'python':platform.python_version(),'platform':platform.platform()},'cases':result}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--csv',type=Path);ap.add_argument('--repeats',type=int,default=3)
    ap.add_argument('--select',help='comma-separated workload names; omitted runs the full corpus')
    args=ap.parse_args()
    if args.repeats<1:raise ValueError('repeats must be positive')
    result=run(args.repeats, set(args.select.split(',')) if args.select else None);args.output.write_text(json.dumps(result,indent=2)+'\n')
    if args.csv:
        with args.csv.open('w',newline='') as f:
            writer=csv.writer(f);writer.writerow(['case','width','W','powered_ms','one_sided_ms','two_sided_ms','one_sided_over_powered'])
            for x in result['cases']:
                c=x['workload'];m=x['median_seconds']
                writer.writerow([c['name'],c['width'],c['repetitions'],1000*m['powered'],1000*m['one_sided_scan'],
                                 1000*m['two_sided_scan'],x['speedup_vs_one_sided']])

if __name__=='__main__':main()
