#!/usr/bin/env python3
"""Paired A/A/B/B timings against the byte-verified archived implementation.

All four arms in a block are randomly permuted.  Each call receives a fresh
Diagram object, so caches do not pass from one arm to another.  Input parsing
and generation are excluded.  Nine blocks give a distribution-free 96.1%
order-statistic interval [second, penultimate] for the median paired ratio,
under the usual independent-block interpretation; raw values and A/A controls
are always retained.  These intervals describe this run, not every platform.
"""
from __future__ import annotations
import argparse
import gc
import hashlib
import importlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.filters import alexander_obstruction
from fastunknot.interlace import visible_factors_interlacement
from verify_factorization import cyclic_trefoil_sum, structural_work


def load_baseline():
    name = '_progress_baseline'
    module = types.ModuleType(name)
    module.__path__ = [str(ROOT/'baseline/fast/fastunknot')]
    module.__package__ = name
    sys.modules[name] = module
    return (importlib.import_module(name+'.diagram').Diagram,
            importlib.import_module(name+'.factor').visible_factors,
            importlib.import_module(name+'.filters').alexander_obstruction,
            importlib.import_module(name+'.recognize').recognize)


def median_interval(values):
    data = sorted(values)
    if len(data) == 9:
        return [data[1], data[-2]], 0.9609375
    return [data[0], data[-1]], 1-2**(1-len(data))


def paired(name, a, b, rounds, rng, signature, metadata):
    # Pilot once each, then select a common loop count for the fast cases.
    pilots = []
    for fun in (a,b):
        start=time.perf_counter()
        result=fun()
        pilots.append(time.perf_counter()-start)
    expected=signature(a())
    assert signature(b()) == expected
    loops=max(1,min(40,int(0.004/max(pilots))))
    raw=[]
    for block in range(rounds):
        arms=['A0','A1','B0','B1']
        rng.shuffle(arms)
        times={}
        for arm in arms:
            gc.collect()
            fun=a if arm.startswith('A') else b
            start=time.perf_counter_ns()
            for _ in range(loops):
                result=fun()
            elapsed=(time.perf_counter_ns()-start)*1e-9/loops
            assert signature(result) == expected
            times[arm]=elapsed
        aa=times['A1']/times['A0']
        ratio=statistics.mean([times['B0'],times['B1']])/statistics.mean([times['A0'],times['A1']])
        raw.append({'block':block,'order':arms,'seconds':times,'ratio':ratio,'aa_ratio':aa})
    ratios=[row['ratio'] for row in raw]
    aa=[row['aa_ratio'] for row in raw]
    interval,coverage=median_interval(ratios)
    return dict(metadata,name=name,rounds=rounds,loops_per_arm=loops,
                result_signature=expected,ratio_median=statistics.median(ratios),
                ratio_interval=interval,interval_nominal_coverage=coverage,
                aa_ratio_median=statistics.median(aa),
                aa_iqr=[statistics.quantiles(aa,n=4)[0],statistics.quantiles(aa,n=4)[2]],
                baseline_seconds_median=statistics.median([r['seconds'][k] for r in raw for k in ('A0','A1')]),
                improved_seconds_median=statistics.median([r['seconds'][k] for r in raw for k in ('B0','B1')]),
                raw=raw)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds',type=int,default=9)
    parser.add_argument('--largest-sum',type=int,default=512)
    parser.add_argument('--kinds',nargs='+',choices=['factorization','alexander','pipeline'],
                        default=['factorization','alexander','pipeline'])
    parser.add_argument('--output',type=Path,default=ROOT/'data/paired_benchmarks.json')
    args=parser.parse_args()
    if args.rounds < 4:
        raise ValueError('at least four blocks are needed')
    OldDiagram,old_factor,old_alexander,old_recognize=load_baseline()
    rng=random.Random(2026100791)
    report={'python':sys.version,'platform':platform.platform(),
            'processor':platform.processor(),'timer':'perf_counter_ns',
            'method':'randomized A/A/B/B, fresh Diagram per call, same-process archived namespace',
            'seed':2026100791,'results':[]}
    report['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for base in (ROOT/'fast/fastunknot',ROOT/'baseline/fast/fastunknot')
        for p in sorted(base.glob('*.py'))}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    def record(row):
        report['results'].append(row)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ('name','baseline_seconds_median',
             'improved_seconds_median','ratio_median','ratio_interval')}),flush=True)
    for k in [8,32,128,256,512]:
        if k>args.largest_sum or 'factorization' not in args.kinds:continue
        pd=cyclic_trefoil_sum(k).pd
        record(paired('factor_cyclic_trefoils_'+str(k),
            lambda pd=pd:old_factor(OldDiagram(pd)),
            lambda pd=pd:visible_factors_interlacement(Diagram(pd)),args.rounds,rng,
            lambda result:sorted(d.crossings for d in result[0]),
            {'kind':'factorization','crossings':len(pd),'summands':k,
             'baseline_internal_crossing_visits':structural_work(k)}))
    for q in [31,127,257,521,1031]:
        if 'alexander' not in args.kinds:continue
        pd=Diagram.from_braid(3,[1,2]*q).pd
        counters=[]
        alexander_obstruction(Diagram(pd),backend='sparse',statistics=counters)
        record(paired('alexander_torus_3_'+str(q),
            lambda pd=pd:old_alexander(OldDiagram(pd)),
            lambda pd=pd:alexander_obstruction(Diagram(pd),backend='sparse'),
            args.rounds,rng,lambda result:result,
            {'kind':'alexander','crossings':len(pd),'sparse_counters':counters,
             'auto_uses_sparse':len(pd)>=256}))
    fixtures=[]
    for name in ['conway','hard_unknot_8','kinoshita_terasaka']:
        pd=Diagram.from_json(json.loads((ROOT/'fast/examples'/f'{name}.json').read_text())).pd
        fixtures.append((name,pd))
    fixtures.append(('cyclic_trefoils_128',cyclic_trefoil_sum(128).pd))
    fixtures.append(('cyclic_trefoils_256',cyclic_trefoil_sum(256).pd))
    fixtures.append(('torus_3_521',Diagram.from_braid(3,[1,2]*521).pd))
    for name,pd in fixtures:
        if 'pipeline' not in args.kinds:continue
        record(paired('recognize_'+name,
            lambda pd=pd:old_recognize(OldDiagram(pd)),
            lambda pd=pd:recognize(Diagram(pd)),args.rounds,rng,
            lambda result:result.status,{'kind':'pipeline','crossings':len(pd)}))


if __name__ == '__main__':
    main()
