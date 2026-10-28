#!/usr/bin/env python3
"""Replay authored checks; benchmark reruns are optional and timed separately."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--benchmarks',action='store_true',help='Rerun the five-repeat kernel benchmarks after correctness checks.')
args=parser.parse_args()
(root/'results').mkdir(exist_ok=True)
records=[]
for optimized in (False,True):
    prefix=[sys.executable]+(['-O'] if optimized else [])
    suffix='_optimized' if optimized else ''
    jobs=[('check_modular_cauchy.py','validation'+suffix+'.json'),
          ('check_adaptive_blocks.py','adaptive_checks'+suffix+'.json'),
          ('check_schedules.py','schedule_checks'+suffix+'.json'),
          ('check_modular_independent.py',None),
          ('check_recursive_conditioning_independent.py',None)]
    for filename,output in jobs:
        command=prefix+[str(root/'code'/filename)]
        if output:
            command+=['--output',str(root/'results'/output)]
        result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        parsed=json.loads(result.stdout)
        if parsed.get('status')!='PASS':
            raise SystemExit('Checker did not report PASS: '+filename)
        records.append({'script':filename,'optimized':optimized,'status':'PASS'})
        print(filename+(' [-O]' if optimized else '')+': PASS',flush=True)
for stem in ['validation','adaptive_checks','schedule_checks','independent_modular_validation','recursive_conditioning_independent']:
    a=json.loads((root/'results'/f'{stem}.json').read_text())
    b=json.loads((root/'results'/f'{stem}_optimized.json').read_text())
    a.pop('optimized_python',None);b.pop('optimized_python',None)
    if a!=b:
        raise SystemExit('Normal and optimized result mismatch: '+stem)
if args.benchmarks:
    subprocess.run([sys.executable,str(root/'code/benchmark_kernel.py'),'--repeats','5',
                    '--output',str(root/'results/benchmark_rerun.json')],cwd=root,check=True)
record={'status':'PASS','runs':records,'normal_optimized_results_equal':True,
        'benchmark_rerun':args.benchmarks,'scope':'Local algebra, exact finite arithmetic, schedules and prototypes; no full SAT run or formal-assistant build.'}
(root/'results/replay.json').write_text(json.dumps(record,indent=2)+'\n')
print('All checks passed. Normal and optimized results agree.')
