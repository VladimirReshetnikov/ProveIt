"""Bounded, same-machine comparisons; raw rank and recognition are NOT conflated.

Run: python tools/benchmark.py --seconds 8 --repetitions 5
Times exclude interpreter/import/JSON conversion. Each sample clears topology
caches. Workers are isolated and forcibly stopped after the cooperative budget
plus process overhead. UNKNOWN times are censored observations, not completions.
"""
import argparse
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot import Diagram
from fastunknot.factors import connected_sum


def cases():
    for path in sorted((ROOT/'examples').glob('*.json')):
        yield path.stem,'pipeline',json.loads(path.read_text()),('baseline','accelerated')
    for n in (31,61,121):
        yield f'T(3,{n})','pipeline',{'braid':{'strands':3,'word':[1,2]*n}},('baseline','accelerated')
    for name in ('conway','kinoshita_terasaka','hard_unknot_8','unknot_braid40'):
        data=json.loads((ROOT/'examples'/f'{name}.json').read_text())
        yield name,'rank',data,('baseline','accelerated-no-factors','accelerated')
    for n in (16,64,256):
        data={'braid':{'strands':n+1,'word':list(range(1,n+1))}}
        yield f'curl_family_{n}','rank',data,('baseline','accelerated')
    for n in (64,256,1024):
        data={'braid':{'strands':n+1,'word':list(range(1,n+1))}}
        yield f'order_{n}','order',data,('baseline','accelerated')
    trefoil=Diagram.from_braid(2,[1,1,1])
    for k in (2,4,6,8,16,32):
        data=connected_sum([trefoil]*k).to_json()
        implementations=('baseline','accelerated') if k<=8 else ('accelerated',)
        yield f'trefoil_sum_{k}','rank',data,implementations
    stress=ROOT/'examples'/'stress'/'original_random_5_braid_36.json'
    if stress.exists():
        yield 'original_random_5_braid_36','rank',json.loads(stress.read_text()),('baseline','accelerated-no-factors','accelerated')
        yield 'original_random_5_braid_36','pipeline',json.loads(stress.read_text()),('baseline','accelerated')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds',type=float,default=8)
    parser.add_argument('--repetitions',type=int,default=5)
    parser.add_argument('--output',default=str(ROOT/'results'/'benchmark.json'))
    args=parser.parse_args()
    output={'environment':{'python':sys.version,'platform':platform.platform(),
                           'machine':platform.machine(),'hash_seed':'0'},
            'budget_seconds_per_sample':args.seconds,'max_objects':200000,
            'repetitions_requested':args.repetitions,'rows':[]}
    try:
        output['environment']['cpu']=next(x.split(':',1)[1].strip() for x in
                  Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name'))
    except (OSError,StopIteration):
        pass
    for name,task,data,implementations in cases():
        n=Diagram.from_json(data).crossings
        for implementation in implementations:
            request={'input':data,'implementation':implementation,'task':task,'seconds':args.seconds,
                     'repetitions':args.repetitions,'max_objects':200000}
            row={'case':name,'task':task,'implementation':implementation,'crossings':n}
            start=time.monotonic()
            try:
                proc=subprocess.run([sys.executable,str(ROOT/'tools'/'benchmark_worker.py')],
                                    input=json.dumps(request),text=True,capture_output=True,
                                    timeout=args.seconds*args.repetitions+3,
                                    env=dict(os.environ,PYTHONHASHSEED='0'),cwd=ROOT)
                if proc.returncode:
                    row.update({'result':{'status':'ERROR','reason':proc.stderr},
                                'wall_seconds':time.monotonic()-start})
                else:
                    row.update(json.loads(proc.stdout))
            except subprocess.TimeoutExpired:
                row.update({'result':{'status':'UNKNOWN','reason':'external worker wall timeout'},
                            'wall_seconds':time.monotonic()-start})
            output['rows'].append(row)
            Path(args.output).write_text(json.dumps(output,indent=2)+'\n')
            print(name,task,implementation,n,row.get('median_seconds',row.get('wall_seconds')),
                  row['result']['status'],flush=True)
    # Comparison sanity checks: timeouts are omitted, never counted as an answer.
    groups={}
    for row in output['rows']:
        if row['result']['status'] not in ('UNKNOWN','ERROR'):
            groups.setdefault((row['case'],row['task']),[]).append(row)
    for key,rows in groups.items():
        if key[1]=='rank':
            assert len({r['result']['rank'] for r in rows})==1,key
            assert len({json.dumps(r['result']['by_degree'],sort_keys=True) for r in rows})==1,key
        elif key[1]=='pipeline':
            assert len({r['result']['status'] for r in rows})==1,key
    output['completed_results_agree']=True
    Path(args.output).write_text(json.dumps(output,indent=2)+'\n')

if __name__=='__main__':
    main()
