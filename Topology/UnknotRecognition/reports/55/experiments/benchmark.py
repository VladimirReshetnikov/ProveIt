"""Matched local-query comparisons, with sparse control and A/A timing control.

Not a knot benchmark: all fixtures are supplied interval relations with coordinate
ownership intervals. Input preparation and trace replay are included. Discovery,
geometric reconstruction and final normal-disc validation are excluded in every arm.
"""
import argparse,csv,hashlib,json,platform,random,statistics,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'src'))
from orbit_transfer import compile_transfer
from orbit_transfer.reference import make_trace,eager_histogram,sparse_eager_histogram,literal_components


def fixtures():
    yield 'tiny',41,[(0,27,8,35,1),(4,13,23,32,-1)],4
    for d in (32,128,512):
        n=2**256+333
        yield 'periodic_'+str(d),n,[(0,n-98,97,n-1,1)],d
    n=2**256
    yield 'static_256',n,[],256
    for d in (32,128,512):
        n=4096;rng=random.Random(271828)
        rows=[]
        for _ in range(14):
            width=rng.randrange(10,n//2);a,c=rng.randrange(n-width+1),rng.randrange(n-width+1)
            rows.append((a,a+width-1,c,c+width-1,rng.choice((-1,1))))
        yield 'mixed_'+str(d),n,rows,d
    for d in (64,256,1024):
        period=2**128+51; q=2**128; n=d*(q*period+1)
        yield 'dense_profiles_'+str(d),n,[(0,n-period-1,period,n-1,1)],d
    n=2**256+1
    yield 'reflection_512',n,[(0,n-1,0,n-1,-1)],512


def workload(name,n,rows,d):
    owners=[(j,n*j//d,n*(j+1)//d) for j in range(d)]
    # One distinguished point selects exactly one original orbit. Other scalar
    # observables model a small decision payload; they are not Euler or homology.
    queries=[[(0,1,1)],[(0,n,1)],[(0,n//2,1),(n//2,n,-1)]]
    cuts=sorted({0,n}|{p for _,a,b in owners for p in (a,b)}
                      |{p for query in queries for a,b,_ in query for p in (a,b)})
    proof=make_trace(n,rows)
    def candidate():
        prog=compile_transfer(n,rows,proof,cuts)
        values=[prog.evaluate_intervals(q) for q in queries]
        selected=next(i for i,v in enumerate(values[0]) if v==1)
        return tuple(prog.extract(selected,owners,d))
    def dense():
        intervals=[]
        for j,query in enumerate(queries):
            for a,b,v in query:
                vector=[0]*(d+3);vector[j]=v;intervals.append((a,b,vector))
        for j,a,b in owners:
            vector=[0]*(d+3);vector[j+3]=1;intervals.append((a,b,vector))
        hist=eager_histogram(n,rows,proof,intervals,d+3)
        return next(v[3:] for v in hist if v[0]==1)
    def sparse():
        intervals=[(a,b,{j:v}) for j,q in enumerate(queries) for a,b,v in q]
        intervals += [(a,b,{j+3:1}) for j,a,b in owners]
        hist=sparse_eager_histogram(n,rows,proof,intervals)
        row=next(dict(v) for v in hist if dict(v).get(0)==1)
        return tuple(row.get(j+3,0) for j in range(d))
    prog=compile_transfer(n,rows,proof,cuts)
    expected=candidate()
    assert dense()==sparse()==expected
    if n<100000:
        orbit=next(c for c in literal_components(n,rows) if 0 in c)
        assert expected==tuple(sum(a<=x<b for x in orbit) for _,a,b in owners)
    elif name.startswith('periodic'):
        assert expected==tuple((b-1)//97-(a-1)//97 for _,a,b in owners)
    elif name.startswith('dense_profiles'):
        q=2**128
        assert expected==(q+1,)+(q,)*(d-1)
    elif name.startswith('static'):
        assert expected==(1,)+(0,)*(d-1)
    elif name.startswith('reflection'):
        assert expected==(1,)+(0,)*(d-2)+(1,)
    return dict(name=name,size_bits=n.bit_length(),dimension=d,
                source_pairings=len(rows),stats=prog.stats,
                functions=dict(dense=dense,sparse=sparse,selective=candidate,selective_AA=candidate),
                expected=expected,source=dict(size=hex(n),pairings=[[hex(v) if j<4 else v for j,v in enumerate(r)] for r in rows],
                                            dimension=d))


def main():
    p=argparse.ArgumentParser();p.add_argument('--rounds',type=int,default=7)
    p.add_argument('--output',type=Path,default=ROOT/'results'/'benchmark.json');a=p.parse_args()
    rng=random.Random(261008608);raw=[]; summaries=[]
    for spec in fixtures():
        work=workload(*spec); funcs=work.pop('functions');expected=work.pop('expected')
        # Calibrate only the A/A candidate and use the same batch size for every arm.
        start=time.perf_counter();funcs['selective']();dt=time.perf_counter()-start
        batch=max(1,min(100,int(.025/max(dt,1e-6))))
        for f in funcs.values():assert f()==expected # warmup, not retained as measurements
        per={name:[] for name in funcs}
        for round_ in range(a.rounds):
            order=list(funcs);rng.shuffle(order)
            for arm in order:
                start=time.perf_counter_ns()
                for _ in range(batch):got=funcs[arm]()
                elapsed=(time.perf_counter_ns()-start)/1e9/batch
                assert got==expected
                per[arm].append(elapsed)
                raw.append(dict(case=work['name'],round=round_,arm=arm,batch=batch,seconds=elapsed))
        med={arm:statistics.median(values) for arm,values in per.items()}
        ratios={arm:statistics.median(x/y for x,y in zip(per[arm],per['selective'])) for arm in ('dense','sparse','selective_AA')}
        work.update(median_seconds=med,paired_ratio_to_selective=ratios,batch=batch)
        summaries.append(work)
        print(work['name'],{k:round(v*1e3,3) for k,v in med.items()},ratios,flush=True)
    manifest={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest()
              for f in sorted((ROOT/'src').rglob('*.py'))}
    result=dict(scope=__doc__,seed=261008608,rounds=a.rounds,python=sys.version,
                platform=platform.platform(),summaries=summaries,samples=raw,source_sha256=manifest)
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2))
    with a.output.with_suffix('.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(raw[0]));writer.writeheader();writer.writerows(raw)

if __name__=='__main__':main()
