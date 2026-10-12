"""Paired complete graph construction/query/replay timings; no knot recognition."""
import argparse,gc,json,platform,random,statistics,time
from pathlib import Path
from cycle_kernel import kernel_power,power_explicit,close
from cycle_kernel.query import solve_graph
from cycle_kernel.replay import verify_graph
from families import permuted_prisms,cap_prism

ROOT=Path(__file__).resolve().parent
CASES={'positive-3':('positive',3),'positive-9':('positive',9),'positive-17':('positive',17),
       'positive-33':('positive',33),'negative-3':('negative',3),'negative-64':('negative',64),
       'negative-1024':('negative',1024),'AA-9':('control',9)}

def operation(tile,n,kind):
    g=close(kernel_power(tile,n)[0] if kind=='kernel' else power_explicit(tile,n,cap=20000))
    p=solve_graph(g);assert verify_graph(g,p)
    return dict(vertices=g.n,edges=len(g.edges),verdict=p['verdict'])

def run(case):
    family,n=CASES[case];tile=cap_prism() if family=='negative' else permuted_prisms([2])
    rng=random.Random(2026101241+sum(map(ord,case)))
    arms={'kernel':'kernel','explicit':'explicit'} if family!='control' else {'A':'explicit','B':'explicit'}
    # One warmup round with the same actual operations.
    for arm in arms:gc.collect();operation(tile,n,arms[arm])
    rounds=[]
    for i in range(5):
        order=list(arms);rng.shuffle(order);row={'round':i,'order':order}
        for arm in order:
            gc.collect();start=time.perf_counter_ns();meta=operation(tile,n,arms[arm]);elapsed=time.perf_counter_ns()-start
            row[arm]={'seconds':elapsed/1e9,**meta}
        rounds.append(row)
    names=list(arms);a,b=names
    # Explicit/kernel for the main comparison, B/A for the identical-arm control.
    ratios=[r[b]['seconds']/r[a]['seconds'] for r in rounds]
    result=dict(case=case,source_count=n,family=family,rounds=rounds,
                medians={x:statistics.median(r[x]['seconds'] for r in rounds) for x in arms},
                median_paired_ratio=statistics.median(ratios),python=platform.python_version(),
                platform=platform.platform(),scope='construction + graph query + independent graph-proof replay',
                excluded='input parsing, JSON serialization, spherical/ball validation, native adapter, knot recognition')
    (ROOT/('benchmark-'+case+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(case,result['medians'],'ratio',result['median_paired_ratio'])

def binary():
    tile=permuted_prisms([2]);rows=[]
    for bits in (128,1024,4096,16384):
        n=(1<<bits)+1;operation(tile,n,'kernel');times=[]
        for _ in range(5):
            gc.collect();start=time.perf_counter_ns();meta=operation(tile,n,'kernel');times.append((time.perf_counter_ns()-start)/1e9)
        rows.append(dict(exponent_bits=n.bit_length(),times=times,median_seconds=statistics.median(times),**meta))
    result=dict(rows=rows,scope='kernel construction + graph query + independent graph-proof replay',python=platform.python_version())
    (ROOT/'benchmark-binary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('case',choices=list(CASES)+['binary','all']);args=p.parse_args()
    if args.case=='binary':binary()
    elif args.case=='all':
        for case in CASES:run(case)
        binary()
    else:run(args.case)
