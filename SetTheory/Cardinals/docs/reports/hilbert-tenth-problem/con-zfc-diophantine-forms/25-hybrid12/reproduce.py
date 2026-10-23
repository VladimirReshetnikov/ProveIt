#!/usr/bin/env python3
"""Regenerate and audit this self-contained research package, offline."""
from pathlib import Path
import subprocess
import sys
import json

ROOT=Path(__file__).resolve().parent
STEPS=[('coefficient_builder','coefficients/build_coefficients.py'),
       ('coefficient_independent','coefficients/verify_independent.py'),
       ('arithmetic_builder','arithmetic/build_hybrid12.py'),
       ('arithmetic_independent','verification/audit_hybrid12.py'),
       ('fixed_instance','verification/verify_fixed_instance.py')]

def main():
    receipts=[]
    for name,path in STEPS:
        result=subprocess.run([sys.executable,'-B',str(ROOT/path)],cwd=ROOT,text=True,capture_output=True)
        (ROOT/'verification'/f'{name}.log.txt').write_text(result.stdout+result.stderr)
        receipts.append({'step':name,'path':path,'exit_code':result.returncode})
        print(name+(': PASS' if result.returncode==0 else ': FAIL'),flush=True)
        if result.returncode:
            print(result.stderr[-4000:]);raise SystemExit(result.returncode)
    report={'status':'PASS','python_minimum':'3.10','network_required':False,
            'third_party_python_packages_required':False,'steps':receipts,
            'formal_status':'Ordinary mathematical proofs with finite audits; no new Lean/Rocq endpoint.'}
    (ROOT/'verification/REPRODUCTION.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
