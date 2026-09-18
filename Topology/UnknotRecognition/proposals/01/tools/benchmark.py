#!/usr/bin/env python3
"""Same-machine, cold-process comparisons of the unchanged and optimized engines.
Run: python tools/benchmark.py --output results/benchmark.json
No imports or input conversion are included in kernel times. Each sample gets
its own process. Timeouts are reported as censored, never as completed timings.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def cpu_name():
    try:
        return next(line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                    if line.startswith('model name'))
    except (OSError, StopIteration):
        return platform.processor()


def source_hashes():
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for folder in ('baseline','fast') for p in sorted((ROOT/folder/'fastunknot').glob('*.py'))}


def worker(task):
    # Fix one eligible logical CPU where supported; no concurrent timed workers.
    pinned = None
    if hasattr(os,'sched_getaffinity'):
        pinned=min(os.sched_getaffinity(0)); os.sched_setaffinity(0,{pinned})
    engine=task['engine']
    sys.path.insert(0,str(ROOT/('baseline' if engine=='baseline' else 'fast')))
    import fastunknot
    from fastunknot import scan
    spec=task['input']
    if 'trefoil_sum' in spec:
        k=spec['trefoil_sum']
        d=fastunknot.Diagram.from_braid(k+1,[i for i in range(1,k+1) for _ in range(3)])
    else:
        d=fastunknot.Diagram.from_json(spec)
    for fn in vars(scan).values():
        if hasattr(fn,'cache_clear'):fn.cache_clear()
    kwargs={}
    if engine!='baseline':
        kwargs.update(factor_connected=task.get('factor',False),
                      pivot='lifo' if engine=='cached_lifo' else 'markowitz')
    t=time.perf_counter();started_cpu=time.process_time()
    result={}
    try:
        mode=task['mode']
        if mode=='rank':
            r=scan.khovanov_rank(d.pd,seconds=task['budget'],**kwargs)
            result={'status':'OK','reduced_rank':r['reduced_rank'],'by_degree':r['by_degree'],
                    'stats':r['stats'],'order':r['order']}
        elif mode=='pipeline':
            r=fastunknot.recognize(d,seconds=task['budget'])
            result={'status':r.status,'method':r.method,'reduced_crossings':r.reduced_crossings}
        elif mode=='ordering':
            order=scan.scan_order(d.pd)
            result={'status':'OK','order':order}
        else:raise ValueError('unknown mode')
    except scan.ScanLimit as exc:
        result={'status':'TIMEOUT','reason':str(exc)}
    elapsed=time.perf_counter()-t;cpu=time.process_time()-started_cpu
    result.update(seconds=elapsed,cpu_seconds=cpu,crossings=d.crossings,pinned_cpu=pinned)
    try:
        import resource
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        result['max_rss_bytes']=rss if sys.platform=='darwin' else rss*1024
    except ImportError:pass
    if hasattr(scan,'cache_info'):result['caches']=scan.cache_info()
    print(json.dumps(result))


def cases():
    old=json.loads((ROOT/'baseline/results/benchmark.json').read_text())
    examples=ROOT/'baseline/examples'
    out=[]
    for name in ('conway','kinoshita_terasaka','hard_unknot_8','torus_3_5','unknot_braid40'):
        out.append(dict(name=name,mode='rank',input=json.loads((examples/f'{name}.json').read_text()),budget=15))
    out.append(dict(name='T_2_41',mode='rank',input={'braid':{'strands':2,'word':[1]*41}},budget=15))
    for row in old['scan_families']:
        if ((row['family']=='random 4-braid' and row['crossings'] in (21,31,41))
              or(row['family']=='random 6-braid' and row['crossings']==31)):
            strands=int(row['family'].split()[1].split('-')[0])
            out.append(dict(name=f'random_{strands}_{row["crossings"]}',mode='rank',
                input={'braid':{'strands':strands,'word':row['word']}},budget=15))
    for k in (2,4,6,8,20,50,100):
        out.append(dict(name=f'trefoil_sum_{k}',mode='rank',input={'trefoil_sum':k},
                        factor=True,budget=8,engines=['baseline','fast'] if k<=8 else ['fast']))
    for name in ('conway','kinoshita_terasaka','hard_unknot_8','torus_3_5','trefoil','unknot_braid40',
                 'grid_determinant_one_knot','grid_scrambled_unknot'):
        out.append(dict(name=name,mode='pipeline',input=json.loads((examples/f'{name}.json').read_text()),budget=15))
    for n in (128,256,512,1024):
        out.append(dict(name=f'ordering_{n}',mode='ordering',
                        input={'braid':{'strands':n+1,'word':list(range(1,n+1))}},budget=15))
    row=next(x for x in old['scan_families'] if x['family']=='random 5-braid' and x['crossings']==36)
    out.append(dict(name='random_5_36',mode='rank',input={'braid':{'strands':5,'word':row['word']}},
                    budget=60,engines=['baseline','cached_lifo','fast'],repetitions=1))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker',help=argparse.SUPPRESS)
    parser.add_argument('--output',type=Path,default=ROOT/'results/benchmark.json')
    parser.add_argument('--repetitions',type=int,default=3)
    parser.add_argument('--only',help='substring of case name')
    args=parser.parse_args()
    if args.worker:return worker(json.loads(args.worker))
    report={'python':sys.version,'platform':platform.platform(),'cpu':cpu_name(),
        'timestamp_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'methodology':'fresh process per sample; import/parse/initial validation excluded; cold caches; '
                      'serial workers; fixed allowed CPU when supported; PYTHONHASHSEED=0',
        'sources_sha256':source_hashes(),'cases':[]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for case in cases():
        if args.only and args.only not in case['name']:continue
        row={**case,'samples':{}}
        engines=case.get('engines',['baseline','fast'])
        reps=case.get('repetitions',args.repetitions)
        for repeat in range(reps):
            for engine in engines if repeat%2==0 else list(reversed(engines)):
                if row['samples'].get(engine) and row['samples'][engine][-1]['status']=='TIMEOUT':continue
                task={**case,'engine':engine}
                cmd=[sys.executable,str(Path(__file__).resolve()),'--worker',json.dumps(task)]
                try:
                    completed=subprocess.run(cmd,text=True,capture_output=True,timeout=case['budget']+3,
                                              env=dict(os.environ,PYTHONHASHSEED='0'))
                    if completed.returncode:
                        raise RuntimeError(f'{case["name"]} {engine}: {completed.stderr}')
                    result=json.loads(completed.stdout)
                except subprocess.TimeoutExpired:
                    result={'status':'TIMEOUT','reason':'parent watchdog expired',
                            'budget_seconds':case['budget'],'watchdog_seconds':case['budget']+3}
                row['samples'].setdefault(engine,[]).append(result)
        row['median_seconds']={engine:statistics.median(x['seconds'] for x in samples)
            for engine,samples in row['samples'].items()
            if all(x['status'] in ('OK','UNKNOT','KNOTTED') for x in samples)}
        # No agreement assertion on censored runs. Otherwise require identical task results.
        valid=[sample for samples in row['samples'].values() for sample in samples
               if sample['status'] in ('OK','UNKNOT','KNOTTED')]
        if case['mode']=='rank':
            expected=3**case['input']['trefoil_sum'] if 'trefoil_sum' in case['input'] else None
            if expected is not None:assert all(s['reduced_rank']==expected for s in valid)
            if valid:
                assert all(s['by_degree']==valid[0]['by_degree'] for s in valid),case['name']
        elif case['mode']=='pipeline' and valid:
            assert all(s['status']==valid[0]['status'] for s in valid),case['name']
        elif case['mode']=='ordering' and valid:
            assert all(s['order']==valid[0]['order'] for s in valid),case['name']
        report['cases'].append(row)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        print(case['mode'],case['name'],row['median_seconds'],
              {e:[s['status'] for s in ss] for e,ss in row['samples'].items()},flush=True)

if __name__=='__main__':main()
