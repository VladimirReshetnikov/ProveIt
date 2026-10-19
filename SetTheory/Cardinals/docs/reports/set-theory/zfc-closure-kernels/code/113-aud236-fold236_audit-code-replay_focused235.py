#!/usr/bin/env python3
import argparse,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
binary=a.out/'helper_search'
subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'code/coupled_helper_compensation_terminal.cpp'),'-o',str(binary)],check=True)
records=json.loads((ROOT/'results/focused235_receipt.json').read_text());receipt=[]
for record in records:
    q,r=record['pair'];name=f'focused235_{q}_{r}'
    args=[str(binary)]+[str(ROOT/x) if isinstance(x,str) and x.startswith('input/') else str(x) for x in record['arguments']]
    stdout=a.out/(name+'.txt');stderr=a.out/(name+'.log')
    with stdout.open('w') as out,stderr.open('w') as err:run=subprocess.run(args,stdout=out,stderr=err)
    if run.returncode:raise RuntimeError((name,run.returncode,stderr.read_text()))
    if stdout.read_bytes()!=(ROOT/'results'/(name+'.txt')).read_bytes():raise AssertionError(('candidate output changed',name))
    last=stderr.read_text().splitlines()[-1]
    if not last.startswith('FINISHED'):raise AssertionError(('incomplete',name))
    receipt.append({'pair':[q,r],'returncode':run.returncode,'final_log':last,'candidate_output_matches':True});print(json.dumps(receipt[-1]),flush=True)
(a.out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
