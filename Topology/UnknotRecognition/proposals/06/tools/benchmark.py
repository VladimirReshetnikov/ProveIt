#!/usr/bin/env python3
"""Reproduce sequential, fresh-process, same-interpreter comparisons.

Usage: python tools/benchmark.py [--repeats 3] [--timeout 60] [--select substring]
Writes raw observations and metadata; never treats a timeout as an exact result.
Timing excludes imports and JSON-to-Diagram parsing but includes all work within
khovanov_rank / recognize. Rank() in the new version revalidates its input.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repeats',type=int,default=3)
    p.add_argument('--timeout',type=float,default=60)
    p.add_argument('--select',default='')
    p.add_argument('--output',default='results/benchmarks.json')
    args=p.parse_args()
    if args.repeats < 1 or args.timeout <= 0: p.error('positive limits required')
    fixtures=json.loads((ROOT/'results/fixtures.json').read_text())
    observations=[]
    data={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'python':sys.version,'platform':platform.platform(),
          'machine':platform.machine(),'processor':platform.processor(),
          'hash_seed':'0','timing':'perf_counter around API call, excludes imports and parsing',
          'cooperative_limit_seconds':args.timeout,'hard_limit_seconds':args.timeout+5,
          'peak_rss_units':'KiB on Linux; bytes on macOS; null when unavailable',
          'observations':observations}
    if Path('/proc/cpuinfo').exists():
        data['cpu_model']=next((line.split(':',1)[1].strip() for line in
                              Path('/proc/cpuinfo').read_text().splitlines()
                              if line.startswith('model name')),'unknown')
    output=ROOT/args.output;output.parent.mkdir(parents=True,exist_ok=True)
    for case in fixtures:
        if args.select and args.select not in case['id']:continue
        for variant in case['variants']:
            for repeat in range(min(args.repeats,variant.get('repeats',args.repeats))):
                job={'input':case['input'],'mode':case['mode'],'seconds':args.timeout,
                     'version':variant['version'],'kwargs':variant.get('kwargs',{})}
                started=time.perf_counter()
                try:
                    proc=subprocess.run([sys.executable,str(ROOT/'tools/benchmark_worker.py'),
                                         json.dumps(job)],cwd=ROOT,capture_output=True,text=True,
                                        timeout=args.timeout+5,
                                        env={**os.environ,'PYTHONHASHSEED':'0'})
                    if proc.returncode:
                        result={'status':'ERROR','stderr':proc.stderr,'returncode':proc.returncode}
                    else:result=json.loads(proc.stdout)
                except subprocess.TimeoutExpired:
                    result={'status':'HARD_TIMEOUT','process_limit_seconds':args.timeout+5}
                result.update({'case':case['id'],'mode':case['mode'],'variant':variant['name'],
                               'version':variant['version'],'repeat':repeat,
                               'process_seconds':time.perf_counter()-started})
                observations.append(result)
                output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
                print(case['id'],variant['name'],repeat,result['status'],
                      round(result.get('seconds',result['process_seconds']),6),flush=True)
                if result['status'] in ('UNKNOWN','HARD_TIMEOUT','ERROR'):break
    # Compare all completed ranks by degree, not just their sum.
    for case in fixtures:
        rows=[x for x in observations if x['case']==case['id']]
        ranks=[x for x in rows if x['status']=='EXACT']
        if any(x['by_degree'] != ranks[0]['by_degree'] for x in ranks):
            raise AssertionError('degree mismatch: '+case['id'])
        verdicts={x['status'] for x in rows if x['status'] in ('UNKNOT','KNOTTED')}
        if len(verdicts)>1:raise AssertionError('verdict mismatch: '+case['id'])
    data['completed_comparisons_agree']=True
    output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
