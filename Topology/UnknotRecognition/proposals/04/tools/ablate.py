"""Isolate pivot choice with the same optimized algebra, cold processes."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--timeout',type=float,default=10)
    p.add_argument('--repeats',type=int,default=3)
    args=p.parse_args()
    results=[]
    for case in ('conway.json','kinoshita_terasaka.json','five_braid_36.json'):
        path=ROOT/('fast/examples' if case!='five_braid_36.json' else 'benchmarks/inputs')/case
        for strategy in ('stack','minfill'):
            samples=[]
            for _ in range(args.repeats):
                cmd=[sys.executable,str(ROOT/'tools/bench_worker.py'),'fast','scan',str(path),
                     '--seconds',str(args.timeout),'--pivot-strategy',strategy]
                try:
                    run=subprocess.run(cmd,capture_output=True,text=True,timeout=args.timeout+3)
                    sample=json.loads(run.stdout) if run.returncode==0 else {
                        'status':'ERROR','stderr':run.stderr}
                except subprocess.TimeoutExpired:
                    sample={'status':'EXTERNAL_TIMEOUT'}
                samples.append(sample)
                if sample['status']!='OK':break
            group={'input':case,'strategy':strategy,'samples':samples}
            if all(s['status']=='OK' for s in samples):
                group['median_seconds']=statistics.median(s['wall_seconds'] for s in samples)
            else:group['censoring_seconds']=args.timeout
            results.append(group)
            print(case,strategy,group.get('median_seconds',f"> {args.timeout}s"),flush=True)
    data={'generated_utc':datetime.now(timezone.utc).isoformat(),'python':sys.version,
          'platform':platform.platform(),'groups':results}
    (ROOT/'benchmarks/ablation.json').write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
