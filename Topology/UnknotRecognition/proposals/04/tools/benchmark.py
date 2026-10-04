"""Cold-process benchmarks against the unchanged supplied baseline.

Run from anywhere: python tools/benchmark.py --repeats 3 --timeout 30
Censored cases are attempted only once. All successful cases are repeated.
JSON/PD validation, imports and process launch are outside the recorded timer.
"""
from __future__ import annotations
import argparse
import csv
from datetime import datetime, timezone
import json
import os
import platform
from pathlib import Path
import statistics
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]

def run(implementation,operation,path,timeout):
    cmd=[sys.executable,str(ROOT/'tools/bench_worker.py'),implementation,operation,str(path),
         '--seconds',str(timeout)]
    try:
        p=subprocess.run(cmd,capture_output=True,text=True,timeout=timeout+3)
        if p.returncode:
            return {'status':'ERROR','stderr':p.stderr,'stdout':p.stdout,
                    'implementation':implementation,'operation':operation,'input':path.name}
        return json.loads(p.stdout)
    except subprocess.TimeoutExpired:
        return {'status':'EXTERNAL_TIMEOUT','wall_seconds_lower_bound':timeout,
                'implementation':implementation,'operation':operation,'input':path.name}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats',type=int,default=3)
    parser.add_argument('--timeout',type=float,default=30)
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--output',default='benchmarks/comparison.json')
    args=parser.parse_args()
    examples=ROOT/'fast/examples';fixtures=ROOT/'benchmarks/inputs'
    tasks=[]
    for name in ('conway','kinoshita_terasaka','hard_unknot_8','trefoil',
                 'figure_eight','torus_3_5','grid_scrambled_unknot','unknot_braid40'):
        tasks += [(impl,'recognize',examples/f'{name}.json') for impl in ('baseline','fast')]
    for name in ('conway','kinoshita_terasaka','hard_unknot_8','torus_3_5'):
        tasks += [(impl,'scan',examples/f'{name}.json') for impl in ('baseline','fast')]
    if not args.quick:
        for name in ('four_braid_41','five_braid_36','conway_sum2','conway_sum3'):
            tasks += [(impl,'recognize',fixtures/f'{name}.json') for impl in ('baseline','fast')]
        for name in ('four_braid_41','five_braid_36','conway_sum2'):
            tasks += [(impl,'scan',fixtures/f'{name}.json') for impl in ('baseline','fast')]
        for name in ('conway_sum2','conway_sum3','conway_sum8','conway_sum16',
                     'trefoil_sum8','trefoil_sum16'):
            tasks.append(('fast','factored',fixtures/f'{name}.json'))
        for n in (128,256,512,1024):
            tasks += [(impl,'order',fixtures/f'unknot_chain{n}.json') for impl in ('baseline','fast')]
        for n in (128,256):
            tasks += [(impl,'scan',fixtures/f'unknot_chain{n}.json') for impl in ('baseline','fast')]
    data={'generated_utc':datetime.now(timezone.utc).isoformat(),
          'python':sys.version,'platform':platform.platform(),'processor':platform.processor(),
          'cpu_count':os.cpu_count(),'timeout_seconds':args.timeout,
          'requested_repeats':args.repeats,'cold_processes':True,
          'timing_excludes':'imports, process start, input parsing, Diagram validation',
          'groups':[]}
    dest=ROOT/args.output;dest.parent.mkdir(parents=True,exist_ok=True)
    for implementation,operation,path in tasks:
        samples=[]
        for repeat in range(args.repeats):
            sample=run(implementation,operation,path,args.timeout)
            samples.append(sample)
            if sample['status'] not in ('OK','UNKNOT','KNOTTED'):
                break
        successful=all(s['status'] in ('OK','UNKNOT','KNOTTED') for s in samples)
        group={'implementation':implementation,'operation':operation,'input':path.name,
               'successful':successful,'samples':samples}
        if successful:
            group['median_seconds']=statistics.median(s['wall_seconds'] for s in samples)
            group['minimum_seconds']=min(s['wall_seconds'] for s in samples)
            group['maximum_seconds']=max(s['wall_seconds'] for s in samples)
        else:
            group['censoring_seconds']=args.timeout if all(
                s['status'] in ('LIMIT','UNKNOWN','EXTERNAL_TIMEOUT') for s in samples) else None
        data['groups'].append(group)
        dest.write_text(json.dumps(data,indent=2)+'\n')
        print(implementation,operation,path.name,
              f"{group['median_seconds']:.6f}s" if successful else samples[-1]['status'],flush=True)
    rows=[]
    for g in data['groups']:
        rows.append({k:g.get(k) for k in ('implementation','operation','input','successful',
                                        'median_seconds','minimum_seconds','maximum_seconds','censoring_seconds')})
    csvpath=dest.with_suffix('.csv')
    with csvpath.open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    print('Saved',dest,'and',csvpath)

if __name__=='__main__':main()
