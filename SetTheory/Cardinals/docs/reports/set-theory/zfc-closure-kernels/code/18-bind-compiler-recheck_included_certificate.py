#!/usr/bin/env python3
"""Offline recheck of the included 4533-pair register-program certificate.

Uses only Python's standard library, included JSON inputs, and the unchanged
attributed prior independent path engine. Does not import the compiler or
grammar generator, require ProveIt, or fetch anything from the network.
Executable finite verification is not a proof-assistant or binary-TM theorem.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
PINS={
    'independent_verifier/verify_rm_certificate.py':
        '30fbd95b7a2a61004422558cfab4419de5239b67b88bc9ed19b7de8fcf585f18',
    'independent_verifier/verify_schema_rm_certificate.py':
        'e71042fcb1977ea4945567f1f7d3a0a0a0fa0d431360bd59d5dba76d8f28a872',
    'original-reference-dag.json':
        'fc5dad5869328a2f85a78ad725f4726ebf2870a4e9ee13a63d2009f7ef0af7fc',
    'original-dag.json':
        '55a7dcad13f4a226d079128afab68aa00cf2c047a196444c643d2b42859a37f2',
    'original-rm-bisimulation.json':
        '920df8e044536e0bfdc57fc592e6374cc82943a8599aef615df42ca802984003',
}

def run(certificate):
    return subprocess.run([
        sys.executable,'-E','-B',str(ROOT/'independent_verifier/verify_schema_rm_certificate.py'),
        '--prior-machine-dir',str(ROOT/'independent_verifier'),
        '--reference',str(ROOT/'original-reference-dag.json'),
        '--candidate',str(ROOT/'original-dag.json'),
        '--certificate',str(certificate)],capture_output=True,text=True,check=False)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test',action='store_true',help='also reject a swapped decrement-branch certificate')
    ap.add_argument('--output',type=Path,help='optional JSON evidence destination')
    a=ap.parse_args()
    if not __debug__:
        raise RuntimeError('Do not use Python -O: the attributed checker uses assertions')
    for name,digest in PINS.items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('pinned certificate input or independent engine changed: '+name)
    result=run(ROOT/'original-rm-bisimulation.json')
    if result.returncode:
        raise RuntimeError('independent certificate verification failed:\n'+result.stderr)
    evidence=json.loads(result.stdout)
    expected={'verified':True,'reference_nodes':219,'candidate_nodes':207,'related_pairs':4533,
        'instruction_counts':{'EDecnz':1931,'EInc':2601,'EHalt':1}}
    for key,value in expected.items():
        if evidence.get(key)!=value:raise AssertionError('unexpected result: '+key)
    evidence['offline']=True
    evidence['requires_repository_checkout']=False
    evidence['generator_or_compiler_imported']=False
    if a.self_test:
        mutant=json.loads((ROOT/'original-rm-bisimulation.json').read_text())
        for rec in mutant['pairs']:
            if rec['instruction'].startswith('EDecnz ') and rec['successors'][0]!=rec['successors'][1]:
                rec['successors'].reverse()
                break
        else:raise AssertionError('no distinct decrement branches for negative control')
        with tempfile.TemporaryDirectory(prefix='rm-certificate-negative-') as temp:
            path=Path(temp)/'swapped-branches.json';path.write_text(json.dumps(mutant))
            rejected=run(path)
            if rejected.returncode==0:raise AssertionError('swapped-branch certificate was accepted')
        evidence['swapped_decrement_branches_rejected']=True
    text=json.dumps(evidence,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
