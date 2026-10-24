#!/usr/bin/env python3
"""Independently replay all monic inverses and collect every quartic coefficient.

Imports the separately authored upstream projection and polynomial verifiers,
never the producer or optimizer. Source/Pell completeness is checked separately
by independent_source_check.py and proved in PROOF.md.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source'))
from verify_projection import verify
from independent_polynomial import verify_expansion

def need(ok,message):
    if not ok:raise ValueError(message)
def load(path):return json.loads(path.read_text())

def rejected(fn):
    try:fn()
    except (ValueError,KeyError):return True
    return False

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant',type=int,default=63)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    root=HERE/'variants'/str(args.variant)
    parent=load(root/'parent.json')
    census=load(root/'CENSUS.json')
    need(parent['domain']=='unrestricted integers','signed parent domain')
    results={}
    for name in census:
        child=load(root/name/'equation.json')
        cert=load(root/name/'projection.json')
        expanded=load(root/name/'polynomial.json')
        need(cert['unconstrained_removed']==[],'all removed coordinates have integer restorations')
        report=verify(parent,child,cert)
        report['whole_polynomial']=verify_expansion(child,expanded)
        need(child['metrics']==census[name],'exact whole metrics')
        need(report['whole_polynomial']['exact_degree']==4,'exact quartic degree')
        changed=deepcopy(cert)
        changed['steps'][0]['restoration'][0][0]+=1
        need(rejected(lambda:verify(parent,child,changed,check_hashes=False)),
             'altered integer restoration rejected')
        changed=deepcopy(expanded)
        changed['terms'][0][0]+=1
        need(rejected(lambda:verify_expansion(child,changed)),
             'altered whole coefficient rejected')
        report['negative_controls']=['changed restoration','changed quartic coefficient']
        results[name]=report
    result=dict(status='PASS',variant=args.variant,
                scope='All integer monic restorations and every expanded quartic coefficient; no optimizer imported',
                parent_sha256=sha256((root/'parent.json').read_bytes()).hexdigest(),
                optimized_python=not __debug__,profiles=results)
    output=args.output or root/('CHECKS_OPTIMIZED.json'if not __debug__ else'CHECKS.json')
    output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':main()
