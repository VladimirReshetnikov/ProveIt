#!/usr/bin/env python3
"""Regenerate all finite artifacts without network access or third-party Python.

The verification receipt is not a machine-checked proof of the semantic
equivalence or a proof of consistency. See report.tex for that distinction.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
SCRIPTS=[
    'compiler/build_complemented.py',
    'compiler/audit_complemented.py',
    'nine/build_nine.py',
    'nine/bind_coefficients.py',
    'nine/verify_nine.py',
    'signed10/build.py',
    'signed10/verify.py',
    'eleven/build_eleven.py',
    'eleven/check_eleven.py',
    'eleven/build_eleven_translated.py',
    'eleven/check_eleven_translated.py',
]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf',action='store_true',help='Also compile report.tex twice with pdflatex.')
    args=parser.parse_args()
    if sys.version_info<(3,10): raise SystemExit('Python3.10 or later is required.')
    environment=dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE']='1'
    provenance=json.loads((ROOT/'provenance/SOURCE_PROVENANCE.json').read_text())
    for row in provenance['copied_sources']:
        assert hashlib.sha256((ROOT/row['local_path']).read_bytes()).hexdigest()==row['sha256'],row['local_path']
    export=json.loads((ROOT/'compiler/k215_transitions.json').read_text())
    machine=(ROOT/'provenance/k215.tm').read_bytes()
    assert hashlib.sha256(machine).hexdigest()==export['source_sha256']['tm']
    transitions=[]
    for line in machine.decode().splitlines():
        if not line.strip() or line.startswith('#'):continue
        state,read_bit,write_bit,direction,next_state=line.split()
        transitions.append([int(state),int(read_bit),int(write_bit),-1 if direction=='L' else 1,int(next_state)])
    assert transitions==export['transitions'] and len(transitions)==430
    print('Pinned source hashes and all430 literal K215 transitions: PASS',flush=True)
    receipts=[]
    for script in SCRIPTS:
        print('Running '+script,flush=True)
        completed=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,
            env=environment,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        receipts.append({'script':script,'exit_code':completed.returncode})
        if completed.returncode:
            print(completed.stdout)
            raise SystemExit(completed.returncode)
        print('  PASS',flush=True)
    if args.pdf:
        for pass_number in (1,2):
            print('Compiling report.pdf, pass '+str(pass_number),flush=True)
            completed=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                '-file-line-error','report.tex'],cwd=ROOT,text=True,
                stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            if completed.returncode:
                print(completed.stdout)
                raise SystemExit(completed.returncode)
    receipt={'status':'PASS','source_pin':'22e75dd6b87b1b199bb08c778d7cf075ae5aae08',
        'scope':'Finite builders, arithmetic/data certificates and implementation checks. The unbounded equivalence uses report proofs and identified inherited theorems.',
        'scripts':receipts,
        'source_identity':{'copied_source_hashes':len(provenance['copied_sources']),
            'literal_K215_transitions_matched':430},
        'detailed_receipts':['compiler/INDEPENDENT_AUDIT.json','nine/generated/VERIFICATION.json',
            'nine/generated/DEGREE_CERTIFICATE.json','signed10/generated/VERIFICATION.json',
            'eleven/generated/CHECK_RESULTS.json','eleven/generated/TRANSLATED_CHECK_RESULTS.json']}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('All finite checks passed. See VERIFICATION.json and report.pdf.')


if __name__=='__main__': main()
