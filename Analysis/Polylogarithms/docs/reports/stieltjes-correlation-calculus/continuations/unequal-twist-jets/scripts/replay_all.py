#!/usr/bin/env python3
"""Rerun all suites at 65 and 85 digits and preserve both records."""
from __future__ import annotations
import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--precisions',type=int,nargs='+',default=[65,85])
    args=parser.parse_args();summary=[]
    for dps in args.precisions:
        if dps<55:parser.error('Precisions must be at least 55 decimal digits.')
        for script,extra in [('verify.py',['--part','all']),('verify_extended.py',[])]:
            subprocess.run([sys.executable,str(ROOT/'scripts'/script),*extra,'--dps',str(dps)],
                           check=True,cwd=ROOT,timeout=600)
        target=ROOT/'validation'/f'dps{dps}';target.mkdir(parents=True,exist_ok=True)
        data={}
        for name in ['exact','spectral','scalar','gamma','extended']:
            path=ROOT/'validation'/f'{name}.json'
            shutil.copy2(path,target/path.name)
            data[name]=json.loads(path.read_text())
        exact=data['exact']['total']+data['extended']['exact']['count']
        numeric=sum(data[name]['count'] for name in ['spectral','scalar','gamma'])+data['extended']['numerical']['count']
        summary.append({'dps':dps,'exact_assertions':exact,'numerical_comparisons':numeric,'passed':True})
    (ROOT/'validation'/'replay-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
