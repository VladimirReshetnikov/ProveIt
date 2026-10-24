#!/usr/bin/env python3
"""Rebuild, replay and independently expand the direct natural equations."""
from __future__ import annotations
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'provenance/upstream')]
from affine_contract import contract,independent_verify,polynomial_and_metrics
from verify_synchronized import exact_expansion
from audit_bootstrap import audit

def need(ok,message):
    if not ok:raise ValueError(message)

def read(p):return json.loads(p.read_text())

def run():
    result=audit()
    flags=[] if __debug__ else ['-O']
    with tempfile.TemporaryDirectory(prefix='con-zfc-bootstrap-') as temp:
        files=['equation.json','expanded_polynomial.json','majorant_certificate.json',
               'macro_inventory.json','factorial_radius_certificate.json','index_shift_certificate.json']
        result['parent_rebuilt_byte_identical_files']={}
        result['contractions']={}
        variants=[('square','parent781',[(64,'natural469'),(256,'natural468')]),
                  ('linear','parent783',[(256,'natural467')])]
        for mode,parent_name,targets in variants:
            parent=Path(temp)/parent_name
            p=subprocess.run([sys.executable,*flags,str(ROOT/'code/bootstrap_builder.py'),
                              '--radius',mode,'--output',str(parent)],text=True,capture_output=True)
            need(p.returncode==0,'parent rebuild failed: '+p.stdout+p.stderr)
            for filename in files:
                need((parent/filename).read_bytes()==(ROOT/'equations'/parent_name/filename).read_bytes(),
                     'parent byte comparison failed: '+parent_name+'/'+filename)
            source=read(parent/'equation.json')
            result['parent_rebuilt_byte_identical_files'][parent_name]=files
            for cap,name in targets:
                target,certificate=contract(source,support_cap=cap,terminal_quadratic=True)
                d=ROOT/'equations'/name
                need(target==read(d/'equation.json'),'contraction equation differs: '+name)
                need(certificate==read(d/'elimination_certificate.json'),'contraction certificate differs: '+name)
                receipt=independent_verify(source,target,certificate)
                polynomial,metrics=polynomial_and_metrics(target['residuals'],len(target['variables']))
                need(polynomial==read(d/'expanded_polynomial.json'),'expanded polynomial differs: '+name)
                receipt['independent_expansion']=exact_expansion(target,polynomial)
                result['contractions'][name]=receipt
        bad=deepcopy(read(ROOT/'equations/natural467/expanded_polynomial.json'))
        bad['terms'][0][0]+=1
        try:exact_expansion(target,bad)
        except ValueError:pass
        else:raise ValueError('corrupt expanded coefficient accepted')
        cert_bad=deepcopy(certificate);cert_bad['steps'][0]['restoration'][0][0]+=1
        try:independent_verify(source,target,cert_bad)
        except ValueError:pass
        else:raise ValueError('corrupt restoring polynomial accepted')
        result['deliberate_corruptions_rejected']=2
    result['status']='PASS'
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=run()
    if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','parent_variables':[781,783],'natural_variables':[469,468,467],
                      'corruptions_rejected':result['deliberate_corruptions_rejected'],
                      'proof_scope':'Ordinary universal proofs plus exact finite artifact audits; no new Lean/Rocq proof.'},indent=2))
