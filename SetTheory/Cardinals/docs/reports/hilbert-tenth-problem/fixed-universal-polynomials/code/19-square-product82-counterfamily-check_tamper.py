#!/usr/bin/env python3
"""Fresh recovery tamper checks. Runs only the newly authored checker."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parent

def same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    if a.output and a.expect:raise ValueError('Choose output or expect')
    cases=[]
    for name in ['source_pin','proof_pin','typed_receipt_false_to_zero']:
        with tempfile.TemporaryDirectory(prefix='recovered-square82-tamper-') as tmp:
            dst=Path(tmp)
            for f in ['check_counterfamily.py','COUNTERFAMILY.md','CHECKS.json']:shutil.copyfile(ROOT/f,dst/f)
            shutil.copytree(ROOT/'source',dst/'source')
            if name=='source_pin':
                p=dst/'source/complete82_auxiliary_square_product_chart.json';p.write_bytes(p.read_bytes()+b' ')
                expected='ValueError: source pin complete82_auxiliary_square_product_chart.json'
            elif name=='proof_pin':
                p=dst/'COUNTERFAMILY.md';p.write_bytes(p.read_bytes()+b'\n')
                expected='ValueError: type-exact receipt equality'
            else:
                p=dst/'CHECKS.json';d=json.loads(p.read_text());d['source_contract']['upstream_executed']=0;p.write_text(json.dumps(d))
                expected='ValueError: type-exact receipt equality'
            proc=subprocess.run([sys.executable,'-O',str(dst/'check_counterfamily.py'),'--expect',str(dst/'CHECKS.json')],capture_output=True,text=True)
            error=proc.stderr.splitlines()[-1] if proc.stderr else ''
            if proc.returncode!=1 or error!=expected:raise ValueError('Unexpected tamper result '+name+': '+error)
            cases.append(dict(case=name,detected=True,returncode=proc.returncode,error=error))
    result=dict(status='PASS',self_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),checker_sha256=hashlib.sha256((ROOT/'check_counterfamily.py').read_bytes()).hexdigest(),cases=cases)
    if a.expect and not same(result,json.loads(a.expect.read_text())):raise ValueError('Tamper receipt mismatch')
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',tamper_cases=len(cases)),sort_keys=True))
if __name__=='__main__':main()
