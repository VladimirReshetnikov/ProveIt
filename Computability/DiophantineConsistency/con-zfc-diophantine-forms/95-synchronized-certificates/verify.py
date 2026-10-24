#!/usr/bin/env python3
"""Read-only verification of the delivered mathematical data and reproducibility."""
from __future__ import annotations
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
CODE=ROOT/'code';UP=ROOT/'provenance/upstream'
sys.dont_write_bytecode=True
sys.path[:0]=[str(CODE),str(UP)]
from affine_contract import independent_verify

def need(ok,message):
    if not ok:raise ValueError(message)

def filehash(p):return sha256(p.read_bytes()).hexdigest()

def run(script,args,env):
    command=[sys.executable]+([] if __debug__ else ['-O'])+[str(script)]+list(map(str,args))
    result=subprocess.run(command,capture_output=True,text=True,env=env,cwd=ROOT)
    need(result.returncode==0,'audit failed: '+script.name+'\n'+result.stdout+result.stderr)
    return json.loads(result.stdout)

def manifest():
    path=ROOT/'MANIFEST.sha256'
    if not path.exists():return {'present':False,'files_checked':0}
    checked=0
    for line in path.read_text().splitlines():
        digest,name=line.split('  ',1)
        rel=Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts,'unsafe manifest path')
        p=ROOT/rel
        need(p.is_file() and filehash(p)==digest,'file digest differs: '+name)
        checked+=1
    return {'present':True,'files_checked':checked}

def source_checks():
    pins=json.loads((UP/'calibration/CALIBRATION_PINS.json').read_text())
    checked=[]
    for entry in pins['files']:
        path=UP/'calibration'/entry['local_file']
        if not path.exists():path=UP/entry['local_file']
        need(filehash(path)==entry['sha256'],'inherited calibration bytes changed: '+entry['local_file'])
        checked.append(entry['local_file'])
    spec=importlib.util.spec_from_file_location('pinned_calculus_audit',UP/'audit_calculus.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    source=json.loads((UP/'wire_eliminated_source.json').read_text())
    branches=[module.verify_branch(b) for b in source['horn_branches']]
    return {'pinned_files':checked,'exact_calculus_branches':branches}

def corruptions():
    source=json.loads((ROOT/'equations/source895/equation.json').read_text())
    target=json.loads((ROOT/'equations/natural522/equation.json').read_text())
    certificate=json.loads((ROOT/'equations/natural522/elimination_certificate.json').read_text())
    results=[]
    for kind in ('restoration_coefficient','pivot_sign','coordinate_order'):
        bad=deepcopy(certificate)
        if kind=='restoration_coefficient':
            step=next(s for s in bad['steps'] if s['restoration'])
            step['restoration'][0][0]+=1
        elif kind=='pivot_sign':bad['steps'][0]['pivot_sign']*=-1
        else:
            values=bad['retained_original_indices_in_target_order'];values[0],values[1]=values[1],values[0]
        try:independent_verify(source,target,bad)
        except ValueError as exc:results.append({'corruption':kind,'rejected':True,'reason':str(exc)})
        else:raise ValueError('corrupt certificate accepted: '+kind)
    return results

def verify():
    result={'status':'PASS','optimized_python':not __debug__,'manifest':manifest(),
            'inherited_source':source_checks()}
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    env['PYTHONPATH']=str(CODE)+os.pathsep+str(UP)
    with tempfile.TemporaryDirectory(prefix='conzfc_verify_') as temporary:
        tmp=Path(temporary)
        structure=run(CODE/'verify_synchronized.py',['--product-index','--factored-source',
            '--equation-dir',ROOT/'equations/source895','--output',tmp/'structure.json'],env)
        result['structural_audit']=structure
        result['product_pell_audit']=run(CODE/'audit_shared_product.py',['--output',tmp/'pell.json'],env)
        result['factored_source_audit']=run(CODE/'audit_factored_source.py',['--output',tmp/'factoring.json'],env)
        result['regeneration']=run(CODE/'release.py',['--output',tmp/'rebuilt'],env)
        delivered={str(p.relative_to(ROOT/'equations')):filehash(p)
                   for p in (ROOT/'equations').rglob('*.json')}
        rebuilt={str(p.relative_to(tmp/'rebuilt')):filehash(p)
                 for p in (tmp/'rebuilt').rglob('*.json')}
        need(delivered==rebuilt,'deterministic equation regeneration differs')
        result['exact_regenerated_files']=len(delivered)
        result['equation_sha256']=dict(sorted(delivered.items()))
    result['corruption_controls']=corruptions()
    result['scope']='Finite literal algebra and provenance checks; ordinary universal proofs and inherited logical calibrations are separate.'
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    result=verify()
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'optimized_python':result['optimized_python'],
        'exact_regenerated_files':result['exact_regenerated_files'],
        'manifest':result['manifest'],'corruption_controls':result['corruption_controls'],
        'equations':result['regeneration']['metrics']},indent=2))

if __name__=='__main__':main()
