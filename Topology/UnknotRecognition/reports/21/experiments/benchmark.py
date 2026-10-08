"""Paired, alternated, freshly initialized comparisons; no third-party packages.

The baseline is the attributed source-derived scanner fixture, NOT a checkout
of the full production pipeline. Synthetic matrices need not arise from knots.
"""
from common import *
from radical import Complex, reduce_complex, snapshot, bits
from fastunknot.planar import Planar
from time import perf_counter_ns
from statistics import median
import argparse, csv, json, platform, random, os


def block_problem(b, m, q, seed=427, sparse=False, scalar_mix=False):
    rng=random.Random(seed)
    alg=Planar(False)
    matching=alg.intern(tuple((2*j,2*j+1) for j in range(b)))
    size=m+q
    out=[{} for _ in range(2*size)]
    # Top-left constant matrix is invertible. Other constant blocks vanish.
    const=[1<<j for j in range(m)]
    if scalar_mix:
        for _ in range(6*m):
            a,c=rng.sample(range(m),2)
            const[a]^=const[c]
    for j in range(size):
        for k in range(size):
            if sparse and j!=k: continue
            value=rng.getrandbits(1<<b) & ~1
            if j<m and k<m and (const[j]>>k)&1: value|=1
            if value: out[j][size+k]=value
    return alg,Complex([matching]*(2*size),[0]*size+[1]*size,out)


def load_scan(c,alg):
    scan=FastScan(shape_cache=False)
    scan.algebra=alg
    scan.mid=c.mid[:]; scan.deg=c.deg[:]
    scan.out=[dict(row) for row in c.out]
    scan.inc=[set() for _ in c.mid]
    for j,row in enumerate(scan.out):
        for k in row: scan.inc[k].add(j)
    scan.live=c.n
    scan.points=frozenset(x for p in alg.pairs[c.mid[0]] for x in p)
    return scan


def timed_block(spec,mode):
    alg,c=block_problem(**spec)
    if mode=='baseline':
        scan=load_scan(c,alg)
        start=perf_counter_ns(); scan.eliminate(); elapsed=perf_counter_ns()-start
        return dict(ns=elapsed,residual=scan.live,compositions=scan.stats['compositions'],
                    algebra_plans=alg.stats['plans'])
    start=perf_counter_ns(); red=reduce_complex(c,alg); elapsed=perf_counter_ns()-start
    return dict(ns=elapsed,**red.stats,algebra_plans=alg.stats['plans'])


def timed_diagram(pd,mode):
    # Complete scanner includes crossing transfer, elimination, and result extraction.
    # PD conversion is equally excluded for every method.
    cls=FastScan if mode=='baseline' else RadicalScan
    kw={} if mode=='baseline' else dict(mode=mode)
    start=perf_counter_ns()
    scan=cls(shape_cache=False,**kw)
    for crossing in pd: scan.add_crossing(crossing)
    ranks=scan.ranks_by_degree()
    if scan.total_rank()!=sum(ranks.values()): raise ArithmeticError('closed rank mismatch')
    elapsed=perf_counter_ns()-start
    return dict(ns=elapsed,ranks=ranks,**scan.stats)


def regular_representation_homology(c,alg):
    """Independent F2 expansion of a two-term square-free-ring complex."""
    if not c.mid:return (0,0)
    if len(set(c.mid))!=1 or set(c.deg)-{0,1}:raise ValueError('requires one-matching two-term complex')
    b=len(alg.pairs[c.mid[0]]);dim=1<<b
    sources=[j for j,h in enumerate(c.deg) if h==0]
    targets={j:k for k,j in enumerate(j for j,h in enumerate(c.deg) if h==1)}
    pivots={}
    for j in sources:
        for S in range(dim):
            col=0
            for k,f in c.out[j].items():
                for T in bits(f):
                    if not S&T:col^=1<<(targets[k]*dim+(S|T))
            while col:
                top=col.bit_length()-1
                if top not in pivots:pivots[top]=col;break
                col^=pivots[top]
    rank=len(pivots)
    return (len(sources)*dim-rank,len(targets)*dim-rank)


def run(repeats=5):
    record=dict(environment=dict(python=platform.python_version(),implementation=platform.python_implementation(),
                   platform=platform.platform(),processor=platform.processor(),pid=os.getpid(),
                   clock='perf_counter_ns',repeats=repeats,seed=427),
                protocol='fresh algebra per timing; alternate method order; inputs built outside timing; no warm caches',
                matrix_cases=[],diagram_cases=[])
    blocks=[('dense-b3-m12-q1',dict(b=3,m=12,q=1)),
            ('dense-b3-m24-q1',dict(b=3,m=24,q=1)),
            ('dense-b3-m40-q1',dict(b=3,m=40,q=1)),
            ('dense-b4-m24-q1',dict(b=4,m=24,q=1)),
            ('dense-b4-m40-q1',dict(b=4,m=40,q=1)),
            ('dense-b4-m24-q4',dict(b=4,m=24,q=4)),
            ('mixed-scalar-b3-m24-q1',dict(b=3,m=24,q=1,scalar_mix=True)),
            ('sparse-diagonal-b4-m40-q1',dict(b=4,m=40,q=1,sparse=True))]
    for name,spec in blocks:
        runs={m:[] for m in ('baseline','radical')}
        for rep in range(repeats):
            for method in (list(runs) if rep%2==0 else list(runs)[::-1]):
                runs[method].append(timed_block(spec,method))
        assert all(r['residual']==2*spec['q'] for rs in runs.values() for r in rs)
        med={k:median(v['ns'] for v in rs)/1e6 for k,rs in runs.items()}
        alg,c=block_problem(**spec)
        expected=regular_representation_homology(c,alg)
        scan=load_scan(c,alg);scan.eliminate()
        red=reduce_complex(c,alg)
        assert regular_representation_homology(snapshot(scan),alg)==expected
        assert regular_representation_homology(red.complex,alg)==expected
        assert any(red.complex.out)
        item=dict(name=name,parameters=spec,runs=runs,median_ms=med,speedup=med['baseline']/med['radical'],
                  verification=dict(regular_representation_homology=expected,residual_differential_nonzero=True))
        record['matrix_cases'].append(item)
        print(name,med,'speedup',item['speedup'],flush=True)
    diagrams=[('trefoil',2,[1]*3),('figure-eight',3,[1,-2]*2),
              ('torus-3-5',3,[1,2]*5),('alternating-3-braid-12',3,[1,-2]*6),
              ('cancelling-3-braid-14',3,[1,2]*3+[-2,-1]*3+[1,2]),
              ('mixed-4-braid-12',4,[1,2,3,-2,1,-3,2,1,-2,3,2,-1]),
              ('positive-4-braid-12',4,[1,2,3]*4)]
    for name,strands,word in diagrams:
        pd=braid_pd(strands,word)
        runs={m:[] for m in ('baseline','always','auto','terminal','adaptive')}
        expected=None
        for rep in range(repeats):
            methods=list(runs); methods=methods[rep%len(methods):]+methods[:rep%len(methods)]
            for method in methods:
                result=timed_diagram(pd,method)
                if expected is None: expected=result['ranks']
                assert result['ranks']==expected,(name,method,result['ranks'],expected)
                runs[method].append(result)
        med={k:median(v['ns'] for v in rs)/1e6 for k,rs in runs.items()}
        item=dict(name=name,strands=strands,word=word,pd=pd,runs=runs,median_ms=med,
                  speedups={k:med['baseline']/v for k,v in med.items()})
        record['diagram_cases'].append(item)
        print(name,med,'speedups',item['speedups'],flush=True)
    return record

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--repeats',type=int,default=5)
    parser.add_argument('--output',default=str(ROOT/'results'/'benchmarks.json'))
    args=parser.parse_args()
    if args.repeats<1: parser.error('repeats must be positive')
    record=run(args.repeats)
    path=Path(args.output);path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(record,indent=2)+'\n')
    with path.with_suffix('.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['kind','case','method','median_ms','speedup_vs_baseline'])
        for c in record['matrix_cases']+record['diagram_cases']:
            for mode,ms in c['median_ms'].items():
                writer.writerow(['matrix' if 'parameters' in c else 'diagram',c['name'],mode,ms,c['median_ms']['baseline']/ms])
