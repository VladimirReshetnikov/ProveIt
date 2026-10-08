"""Paired raw-backend benchmarks. No front-end simplifications or filters."""
import csv, json, random, statistics, sys, time, platform
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'reference_upstream')]
from closure_reset.diagram import braid_pd, validate, canonical
from closure_reset.driver import recognize_pd

def connected_sum(a,b):
    # Cut edge 0 in each planar diagram, and join the four ends in two pairs.
    a=canonical(a); b=canonical(b); off=1+max(x for c in a for x in c)
    b=[tuple(x+off for x in c) for c in b]; rows=[list(c) for c in a+b]
    aa=[(i,j) for i,c in enumerate(rows) for j,x in enumerate(c) if x==0]
    bb=[(i,j) for i,c in enumerate(rows) for j,x in enumerate(c) if x==off]
    rows[bb[0][0]][bb[0][1]]=0; rows[aa[1][0]][aa[1][1]]=off
    return validate(canonical(rows),knot=True)

def corpus():
    trefoil=braid_pd(2,[1]*3); eight=braid_pd(3,[1,-2,1,-2])
    cases=[('trefoil',trefoil),('figure_eight',eight),('positive_2braid_11',braid_pd(2,[1]*11)),
           ('coxeter_24',braid_pd(25,list(range(1,25)))),
           ('cancel_pairs_26',braid_pd(3,[1,-1,2,-2]*6+[1,2]))]
    for size in (6,12,24):
        tail=braid_pd(size+1,list(range(1,size+1)))
        cases.append((f'trefoil_then_curls_{size}',connected_sum(trefoil,tail)))
    return cases

def main():
    rng=random.Random(747); arms={'full':dict(reset=False,frontier_test=False),'frontier':dict(reset=False),'reset':dict(reset=True)}
    rows=[]; raw=[]; details=[]
    for name,pd in corpus():
        times={k:[] for k in arms}; outputs={}
        # Initial verification and warm-up; excluded from measurements.
        for arm,options in arms.items(): outputs[arm]=recognize_pd(pd,max_objects=100000,**options)
        assert all(x['status']==outputs['full']['status'] for x in outputs.values())
        assert outputs['full']['status']!='UNKNOWN'
        for rnd in range(9):
            order=list(arms); rng.shuffle(order)
            for arm in order:
                t=time.perf_counter_ns(); result=recognize_pd(pd,max_objects=100000,**arms[arm]); elapsed=(time.perf_counter_ns()-t)/1e6
                assert result['status']==outputs['full']['status']
                times[arm].append(elapsed); raw.append(dict(case=name,round=rnd,arm=arm,milliseconds=elapsed))
        med={a:statistics.median(v) for a,v in times.items()}
        row=dict(case=name,crossings=len(pd),status=outputs['full']['status'],full_ms=med['full'],frontier_ms=med['frontier'],reset_ms=med['reset'],full_over_reset=med['full']/med['reset'],
                 full_peak=outputs['full']['stats']['peak_objects'],reset_peak=outputs['reset']['stats']['peak_objects'],reset_gap=outputs['reset']['stats']['max_gap'],resets=outputs['reset']['stats']['resets'],
                 reset_scanned=outputs['reset']['stats']['scanned'],pure_nonsingleton=outputs['reset']['stats']['nonsingleton_pure_blocks'])
        rows.append(row); details.append(dict(case=name,pd=pd,outputs=outputs)); print(json.dumps(row),flush=True)
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(dict(pd=pd),indent=2)+'\n')
        (ROOT/'examples'/f'{name}.result.json').write_text(json.dumps(outputs['reset'],indent=2)+'\n')
    payload=dict(python=sys.version,platform=platform.platform(),seed=747,rounds=9,scope='raw backend; preconstructed input; validation and evidence included; fixture not production pipeline',summary=rows,raw=raw)
    (ROOT/'results'/'benchmarks.json').write_text(json.dumps(payload,indent=2)+'\n')
    (ROOT/'results'/'benchmark_certificates.json').write_text(json.dumps(details,indent=2)+'\n')
    with (ROOT/'results'/'benchmarks.csv').open('w') as f:
        wr=csv.DictWriter(f,fieldnames=list(rows[0]));wr.writeheader();wr.writerows(rows)
if __name__=='__main__': main()
