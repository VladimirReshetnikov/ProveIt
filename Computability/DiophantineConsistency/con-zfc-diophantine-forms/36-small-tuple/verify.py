#!/usr/bin/env python3
"""Offline release verification. Does not search for a zero or run K215."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent

def run(label,args):
    start=time.monotonic()
    process=subprocess.run([sys.executable,*args],cwd=ROOT,text=True,
                           stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    result={'label':label,'command':[sys.executable,*args],
            'exit_code':process.returncode,'seconds':round(time.monotonic()-start,3)}
    if process.returncode:
        result['error_output']=process.stdout[-12000:]
        raise RuntimeError(json.dumps(result,indent=2))
    print(label+': PASS',flush=True)
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--rebuild',action='store_true')
    args=parser.parse_args()
    steps=[]
    if args.rebuild:
        steps.append(run('coefficient reconstruction',['coefficients/build_coefficients.py']))
        steps.append(run('positive circuit reconstruction',['positive/build_positive_refinements.py']))
    steps.append(run('baseline binding',['baseline/build_baselines.py']))
    independent=[
        ('independent coefficient audit',['coefficients/audit_coefficients.py']),
        ('positive identities and circuits',['positive/check_positive_refinements.py']),
        ('nine-variable exact algebra',['nine/optimize_combined.py']),
    ]
    with ThreadPoolExecutor(max_workers=3) as pool:
        futures=[pool.submit(run,label,cmd) for label,cmd in independent]
        steps.extend(f.result() for f in futures)
    steps.append(run('coherent Jones rebinding',['nine/rebind_compact.py','--coefficients','coefficients']))
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    pos=json.loads((ROOT/'positive/METRICS.json').read_text())
    nine=json.loads((ROOT/'nine/compact/REBOUND_CHECKS.json').read_text())
    assert binding['d']==1012115
    assert binding['materialization']['total_raw_bytes']==506664
    assert nine['index_exponent']==4058127
    assert nine['exact_degree']==120724*5**32+366
    assert {r['operations'] for r in pos}=={109,103,104,120,114,115}
    # Resolve binding references relative to each recommended circuit.
    files=[ROOT/'baseline/product67.json',ROOT/'baseline/retained16_system59.json']
    files+=sorted((ROOT/'positive/circuits').glob('*.json'))
    files+=sorted((ROOT/'nine/compact').glob('nine31_*.json'))
    for p in files:
        obj=json.loads(p.read_text())
        if p.parent.name=='baseline':ref=obj['coefficient_binding']['file']
        elif p.parent.name=='compact':ref=obj['coefficient_binding']['ports']
        else:
            ref=obj['coefficient_binding']
            if isinstance(ref,dict):ref=ref.get('file') or ref.get('binding')
        assert (p.parent/ref).resolve()==(ROOT/'coefficients/COEFFICIENT_BINDING.json').resolve(),(p,ref)
    receipt={'status':'PASS','source_pin':binding['source_commit'],
             'scope':'Finite arithmetic/interface validation plus exact algebra. Semantic equivalence uses the report proofs and inherited compiler/Pell/Jones/K215 theorems.',
             'steps':steps,'coefficient_instance':binding['instance'],
             'coefficient_raw_bytes':506664,'positive_metrics':pos,
             'nine_metrics':nine,'verified_recommended_circuits':len(files)}
    target=ROOT/'evidence/VERIFICATION.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: all recommended circuits use the same complete fixed compiler tuple.')

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O: exact audit assertions must be enabled.')
    main()
