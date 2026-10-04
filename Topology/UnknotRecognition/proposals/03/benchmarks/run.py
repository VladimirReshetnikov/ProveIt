"""Cold-process A/B benchmarks; no package imports or diagram parsing in timers.

Run from the project root:
    python benchmarks/run.py --profile full --output results/benchmarks.json
The full run includes a 60-second original-backend trial on the hard input.
All trials run sequentially. Each sample uses a new Python interpreter/cache.
"""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
from time import perf_counter

ROOT=Path(__file__).resolve().parents[1]

def make_jobs(profile):
    # Use stored words, never stored timings.
    source=json.loads((ROOT/'benchmarks/upstream-inputs.json').read_text())
    rows=next(value for value in source.values() if isinstance(value,list)
              and any(isinstance(x,dict) and 'word' in x for x in value))
    corpus=[]
    for row in rows:
        if 'word' in row:
            corpus.append({'name':row['family'].replace(' ','_')+'_'+str(row['crossings']),
                           'strands':int(row['family'].split()[1].split('-')[0]),'word':row['word']})
    for n in (32,128,256):
        corpus.append({'name':f'unknot_chain_{n}','strands':n+1,'word':list(range(1,n+1))})
    for n in (11,41):
        corpus.append({'name':f'torus_2_{n}','strands':2,'word':[1]*n})
    for n in (5,11):
        corpus.append({'name':f'torus_3_{n}','strands':3,'word':[1,2]*n})
    names=['conway','kinoshita_terasaka','hard_unknot_8']
    if profile=='smoke':
        corpus=corpus[:2]
    for name in names:
        corpus.append({'name':name,'json':json.loads((ROOT/f'examples/{name}.json').read_text())})
    jobs=[]
    def add(case,phase,backends=('original','optimized'),repeats=3,budget=15):
        for r in range(repeats):
            # Alternate which implementation runs first.
            for backend in (backends if r%2==0 else tuple(reversed(backends))):
                jobs.append(dict(case=case,phase=phase,backend=backend,repeat=r,budget=budget))
    for case in corpus:
        hard=case['name']=='random_5-braid_36'
        if hard:
            add(case,'raw',('original',),repeats=1,budget=60)
            add(case,'raw',('optimized',),repeats=3,budget=15)
        else:
            add(case,'raw')
    for path in sorted((ROOT/'examples').glob('*.json')):
        case={'name':path.stem,'json':json.loads(path.read_text())}
        add(case,'pipeline')
    for k in ((2,4) if profile=='smoke' else (2,4,6,8,10,50)):
        case={'name':f'trefoil_sum_{k}','sum':k}
        if k<=6:add(case,'factor',('original','optimized'),budget=8)
        else:add(case,'factor',('optimized',),budget=15)
    if profile=='full':
        # Deliberately bounded ablations, kept separate from primary comparisons.
        for case in corpus:
            if case['name'] in ('random_4-braid_41','random_5-braid_36','conway'):
                add(case,'raw',('optimized-lifo',),repeats=1,budget=10)
        case=next(x for x in corpus if x['name']=='random_5-braid_36')
        add(case,'raw',('original-markowitz',),repeats=1,budget=60)
        for n in (128,256,512):
            case={'name':f'order_chain_{n}','strands':n+1,'word':list(range(1,n+1))}
            add(case,'ordering')
    if profile=='full':
        for k in (2,3,10,50):
            case={'name':f'conway_sum_{k}','sum':k,'block':'conway'}
            add(case,'factor',('original','optimized') if k==2 else ('optimized',),budget=15)
        case={'name':'conway_sum_3','sum':3,'block':'conway'}
        add(case,'pipeline',('original',),repeats=1,budget=10)
        add(case,'pipeline',('optimized',),repeats=3,budget=15)
    return jobs


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',choices=['smoke','full'],default='smoke')
    parser.add_argument('--output',default='results/benchmarks.json')
    parser.add_argument('--resume',action='store_true',help='continue the same saved run')
    args=parser.parse_args()
    output=ROOT/args.output
    output.parent.mkdir(parents=True,exist_ok=True)
    cpu=''
    if Path('/proc/cpuinfo').exists():
        cpu=next((line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                  if line.startswith('model name')),'')
    data={'metadata':{'utc':datetime.now(timezone.utc).isoformat(),'python':sys.version,
          'platform':platform.platform(),'cpu':cpu,'profile':args.profile,
          'timer':'perf_counter; imports and diagram parsing excluded; scan-order construction included',
          'samples':'fresh process per sample, sequential, alternating A/B order',
          'rss_units':'KiB on Linux; platform-native resource.ru_maxrss elsewhere'},'trials':[]}
    jobs=make_jobs(args.profile)
    if args.resume and output.exists():
        previous=json.loads(output.read_text())
        if previous['metadata']['profile']!=args.profile:
            raise ValueError('cannot resume a different benchmark profile')
        data=previous
    completed=len(data['trials'])
    for i,job in enumerate(jobs):
        if i<completed:continue
        t=perf_counter()
        try:
            p=subprocess.run([sys.executable,str(ROOT/'benchmarks/worker.py')],
                input=json.dumps(job),capture_output=True,text=True,
                timeout=job['budget']+15,env={**os.environ,'PYTHONHASHSEED':'0'})
            if p.returncode:raise RuntimeError(p.stderr)
            result=json.loads(p.stdout)
        except subprocess.TimeoutExpired:
            result={'status':'wall_timeout','seconds':None,
                    'wall_seconds':perf_counter()-t,'result':{},
                    'note':'External timeout includes startup; do not treat it as backend elapsed time.'}
        trial={**job,**result}
        data['trials'].append(trial)
        output.write_text(json.dumps(data,indent=2)+'\n')
        print(f"{i+1}/{len(jobs)} {job['phase']} {job['case']['name']} {job['backend']} "
              f"{trial['status']} {trial['seconds']}",flush=True)
    grouped={}
    for x in data['trials']:
        key=(x['phase'],x['case']['name'],x['backend'])
        grouped.setdefault(key,[]).append(x)
    data['summary']=[]
    for (phase,name,backend),trials in grouped.items():
        good=[x['seconds'] for x in trials if x['status']=='ok']
        entry={'phase':phase,'name':name,'backend':backend,'samples':len(trials),
               'completed':len(good),'median_seconds':statistics.median(good) if good else None,
               'min_seconds':min(good) if good else None,'max_seconds':max(good) if good else None,
               'statuses':[x['status'] for x in trials],
               'rank':trials[0]['result'].get('reduced_rank'),
               'method':trials[0]['result'].get('method')}
        data['summary'].append(entry)
    output.write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
