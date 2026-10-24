#!/usr/bin/env python3
"""Run all standard-library release checks. No network or consistency search."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent


def main():
    commands=[('integer','build_and_verify.py'),('positive/eleven','verify.py'),
              ('positive/twelve','verify.py'),('direct','verify.py'),
              ('.','independent_positive_degree_audit.py')]
    output=ROOT/'verification'
    output.mkdir(exist_ok=True)
    receipts=[]
    for folder,script in commands:
        start=time.monotonic()
        result=subprocess.run([sys.executable,script],cwd=ROOT/folder,text=True,
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        tag=(folder+'_'+script).replace('/','_').replace('.','_')
        (output/(tag+'.stdout.txt')).write_text(result.stdout)
        if result.stderr:
            (output/(tag+'.stderr.txt')).write_text(result.stderr)
        receipt={'component':folder,'script':script,'returncode':result.returncode,
                 'seconds':round(time.monotonic()-start,3)}
        receipts.append(receipt)
        print(json.dumps(receipt),flush=True)
        if result.returncode:
            print(result.stderr,file=sys.stderr)
            raise SystemExit(result.returncode)
    summary={'status':'PASS','python':sys.version.split()[0],
             'commands':receipts,'scope':'Exact finite algebra/data checks and diagnostic examples. Universal semantic claims are in the article and identified source proofs.'}
    (output/'RELEASE_CHECKS.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('PASS: all release checks')


if __name__=='__main__':
    main()
