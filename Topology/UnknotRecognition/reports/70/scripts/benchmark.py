#!/usr/bin/env python3
"""Paired kernel experiments; NOT native recognizer or AHT benchmarks.

All comparison arms are explicit, supplied-model reference strategies.
Times include construction and queries, exclude fixture generation and final
result comparison. Static/sparse/epoch timings do not include certification;
a separate certificate experiment times production and independent replay.
"""
from __future__ import annotations
from dataclasses import replace
from hashlib import sha256
from pathlib import Path
from statistics import median
import json
import platform
import random
import sys
import time
ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'src'), str(ROOT/'tests')]
from affine_orbits import BulkIndex, SparseOverlay, Model, Edge, Weight, Defect
from affine_orbits.certificate import make_certificate
from affine_orbits.checker import verify
from oracle import expanded

RNG = random.Random(261009704)


def signature(o):
    return tuple(sorted(o.histogram.items()))


def fixture(W, K=48, D=3):
    rng = random.Random(261009705)
    edges=(Edge(0,1,-1,13), Edge(1,2,1,17), Edge(2,3,-1,23),
           Edge(0,0,1,W//8), Edge(0,0,-1,0))
    weights=[]
    for j in range(K):
        a = rng.randrange(W)
        b = rng.randrange(a+1,W+1)
        weights.append(Weight(j%4,a,b,tuple(rng.randrange(-4,5) for _ in range(D))))
    return Model(4,W,D,edges,tuple(weights))


def paired(name, arms, parameters, rounds=5):
    labels=list(arms)
    samples={x:[] for x in labels}
    orders=[]
    # One untimed full warmup of every arm, with equality checks.
    reference=None
    for label in labels:
        result=arms[label]()
        if reference is None: reference=result
        assert result==reference, (name, label, 'warmup')
    for j in range(rounds):
        order=labels.copy(); RNG.shuffle(order); orders.append(order)
        for label in order:
            t=time.perf_counter(); result=arms[label](); elapsed=time.perf_counter()-t
            assert result==reference, (name,label,j)
            samples[label].append(elapsed)
    medians={x:median(t) for x,t in samples.items()}
    ratio=median([a/b for a,b in zip(samples['reference'],samples['optimized'])])
    control=median([a/b for a,b in zip(samples['optimized_control'],samples['optimized'])])
    return dict(name=name,parameters=parameters,rounds=rounds,seconds=samples,
                execution_orders=orders,medians=medians,paired_reference_over_optimized=ratio,
                paired_control_over_optimized=control)


def run():
    all_results=[]
    for W in [256,1024,4096,16384]:
        m=fixture(W,K=32)
        def compressed(m=m):
            return tuple(sorted(BulkIndex(m).histogram.items()))
        def expand(m=m):
            return tuple(sorted(expanded(m,[])[0].items()))
        all_results.append(paired(f'static-W-{W}', {'reference':expand,'optimized':compressed,
                   'optimized_control':compressed},dict(W=W,vertices=4,K=32,D=3)))
    W=1<<1024
    m=fixture(W,K=64,D=4)
    rng=random.Random(261009706)
    defects=[Defect(rng.randrange(4),rng.randrange(W),rng.randrange(4),rng.randrange(W),
                   (-1,0,0,0)) for _ in range(96)]
    def sparse_cached():
        i=BulkIndex(m); o=SparseOverlay(i); out=[]
        for d in defects:
            o.add(d); out.append(signature(o))
        return out
    def sparse_rebuilt():
        out=[]
        for j in range(len(defects)):
            i=BulkIndex(m); o=SparseOverlay(i)
            for d in defects[:j+1]: o.add(d)
            out.append(signature(o))
        return out
    all_results.append(paired('sparse-prefix-replay',{'reference':sparse_rebuilt,
                 'optimized':sparse_cached,'optimized_control':sparse_cached},
                 dict(W_bits=1025,vertices=4,K=64,D=4,h=96)))
    # Fixed base, no initial holonomy. Eight divisor drops plus first reflection.
    m=replace(m,edges=m.edges[:3])
    updates=[]
    for j in range(1,9):
        updates.append((1,W>>j))
        updates.extend([(1,3*(W>>j))]*19)
    updates.append((-1,0)); updates.extend([(-1,0)]*39)
    edefects=defects[:24]
    def epochs_cached():
        i=BulkIndex(m); o=SparseOverlay(i); out=[]
        for d in edefects:o.add(d)
        for s,t in updates:
            if i.add_root_map(0,s,t):o.rebase()
            out.append(signature(o))
        return out
    def epochs_rebuilt():
        edges=list(m.edges); out=[]
        for s,t in updates:
            edges.append(Edge(0,0,s,t)); i=BulkIndex(replace(m,edges=tuple(edges)));o=SparseOverlay(i)
            for d in edefects:o.add(d)
            out.append(signature(o))
        return out
    all_results.append(paired('monotone-epoch-rebuilds', {'reference':epochs_rebuilt,
                 'optimized':epochs_cached,'optimized_control':epochs_cached},
                 dict(W_bits=1025,vertices=4,K=64,D=4,h=24,q=len(updates),effective_events=9)))
    # Record a separate complete, large-bit producer+checker run without expansion.
    cert_stats=[]
    for B in (1024,4096,24000):
        m=fixture(1<<B,K=32,D=3)
        ts=[];lengths=[];supports=[]
        for _ in range(3):
            t=time.perf_counter();i=BulkIndex(m);o=SparseOverlay(i)
            o.add(Defect(0,0,3,m.sheets-1,(-1,0,0)))
            c=make_certificate(i,o); assert verify(m,o.defects,c)
            ts.append(time.perf_counter()-t)
            from affine_orbits.core import wire
            lengths.append(len(json.dumps(wire(c),separators=(',',':')).encode()))
            supports.append(len(o.histogram))
        cert_stats.append(dict(exponent=B,sheet_integer_bits=B+1,seconds=ts,median_seconds=median(ts),
                               certificate_bytes=lengths[-1],histogram_support=supports[-1]))
    out=dict(status='PASS',seed=261009704,python=sys.version,platform=platform.platform(),
             rounds=5,scope='Supplied-model orbit kernels, not knot recognition; no AHT comparison.',
             timings='Construction and requested histogram queries; no serialization. Certificate phase stated separately.',
             experiments=all_results,large_bit_certificates=cert_stats,
             source_hashes={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
                            for p in sorted((ROOT/'src').rglob('*.py'))})
    (ROOT/'results/benchmarks.json').write_text(json.dumps(out,indent=2)+'\n')
    for r in all_results:
        print(r['name'],{x:round(1000*t,3) for x,t in r['medians'].items()},
              'paired ratio',round(r['paired_reference_over_optimized'],3),
              'A/A',round(r['paired_control_over_optimized'],3))
    print('certificates',cert_stats)

if __name__=='__main__': run()
