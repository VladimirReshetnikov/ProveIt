"""Paired raw low-window queries on common supplied orders, with A/A controls.

Full homology and a depth-two query have different output contracts. Both
window implementations answer the same interval. Nice-order construction is
excluded from these kernel timings; verification is included in minimal mode.
These are not end-to-end recognition or default-pipeline speedups.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter
from fastunknot import Diagram,khovanov_rank
from fastunknot.minimal_window import khovanov_minimal_window_auto
from fastunknot.nice_order import nice_order,OrderError,certify
from fastunknot.ordering import best_scan_order
from fastunknot.window_scan import khovanov_window


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    rng=random.Random(2026100813)
    cases=[('weaving_14',Diagram.from_braid(3,[1,-2]*7)),
           ('torus_3_4',Diagram.from_braid(3,[1,2]*4)),
           ('padded_trefoil',Diagram.from_braid(2,[1,-1]*12+[1]*3))]
    for name in ('conway','kinoshita_terasaka','stress_braid5_36'):
        cases.append((name,Diagram.from_json(json.loads((Path(__file__).parent/'examples'/(name+'.json')).read_text()))))
    rows=[]
    for name,d in cases:
        try:cert=nice_order(d.pd)
        except OrderError:cert=certify(d.pd,best_scan_order(d.pd))
        order=list(cert.order);expected=khovanov_rank(d.pd,order=order)['by_degree']
        target={h:c for h,c in expected.items() if 0<=h<=2}
        arms=dict(full=lambda:khovanov_rank(d.pd,order=order),
            control=lambda:khovanov_rank(d.pd,order=order),
            support=lambda:khovanov_window(d.pd,0,2,order=order),
            minimal=lambda:khovanov_minimal_window_auto(d,0,2,order=order,mirror=False),
            adaptive=lambda:khovanov_minimal_window_auto(d,0,2,order=order,mirror=False,reduction='adaptive'))
        samples=[];results={}
        for _ in range(7):
            shuffled=list(arms);rng.shuffle(shuffled);times={}
            for arm in shuffled:
                start=perf_counter();result=arms[arm]();times[arm]=perf_counter()-start
                assert result['by_degree']==(expected if arm in ('full','control') else target)
                results[arm]={k:v for k,v in result.items() if k!='stages'}
                if 'window_profile' in results[arm]['stats']:
                    results[arm]['stats']=dict(results[arm]['stats']);results[arm]['stats'].pop('window_profile')
            samples.append(dict(order=shuffled,seconds=times))
        ratios={arm:statistics.median(r['seconds']['full']/r['seconds'][arm] for r in samples) for arm in arms if arm!='full'}
        relative=statistics.median(r['seconds']['support']/r['seconds']['minimal'] for r in samples)
        row=dict(name=name,pd=d.pd,order=order,nice=cert.nice,depth=2,samples=samples,
                 results=results,median_full_over=ratios,median_support_over_minimal=relative)
        rows.append(row)
        print(name,cert.nice,{k:round(v,3) for k,v in ratios.items()},'support/minimal',round(relative,3),flush=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(),seed=2026100813,
        rounds=7,scope=__doc__,cases=rows),indent=2)+'\n')


if __name__=='__main__':main()
