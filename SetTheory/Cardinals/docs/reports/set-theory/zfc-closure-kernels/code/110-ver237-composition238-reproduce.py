#!/usr/bin/env python3
"""Portable replay of the exact238 construction. Standard-library Python only.

Default: direct complete unbounded runtime proof. --quick omits that replay.
--with-guard additionally replays the independent predecessor selector proof.
All new receipts and reconstructed tables go outside the delivered package.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__ or sys.flags.optimize: raise RuntimeError('Run without -O or -OO')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--with-guard',action='store_true')
    args=ap.parse_args()
    out=args.output.resolve()
    if out==ROOT or ROOT in out.parents: raise ValueError('Output must be outside the package')
    if out.exists() and any(out.iterdir()): raise ValueError('Output must be new or empty')
    out.mkdir(parents=True,exist_ok=True)
    environment=dict(os.environ)
    for key in ('PYTHONPATH','PYTHONOPTIMIZE','B245_INPUTS','B245_OUTPUT'): environment.pop(key,None)
    jobs=[];began=time.monotonic()
    manifest=ROOT/'MANIFEST.sha256'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest,name=line.split('  ',1)
            path=(ROOT/name).resolve()
            assert ROOT in path.parents and sha(path)==digest, 'Manifest mismatch: '+name
    def run(name,arguments,receipt,status):
        command=[sys.executable,'-B',*map(str,arguments)]
        start=time.monotonic()
        with (out/(name+'.log')).open('w') as log:
            subprocess.run(command,cwd=ROOT,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=1200)
        data=json.loads(receipt.read_text())
        assert data['status']==status,(name,data.get('status'))
        jobs.append({'name':name,'status':data['status'],'seconds':time.monotonic()-start,
                     'receipt':str(receipt.relative_to(out)),'receipt_sha256':sha(receipt),
                     'log_sha256':sha(out/(name+'.log'))})
        print(name, data['status'], flush=True)
        return data
    run('construction',[ROOT/'build.py','--output',out/'build'],out/'build/construction.json','EXACT_TWO_RECIPE_CONSTRUCTION_PASS')
    run('source_control',[ROOT/'source/check_rotation_certificate.py','--report',out/'source_control.json'],out/'source_control.json','PASS_EXACT_SOURCE_CONTROL_CERTIFICATE')
    run('calibrated_source',[ROOT/'source/calibration/check_source_interface.py','--sites',ROOT/'source/baseline_sites.json',
        '--blank-prefix',ROOT/'reference/boundary239_blank_prefix.json','--output',out/'calibrated_source.json'],out/'calibrated_source.json','EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS')
    run('local238',[ROOT/'verification/certify_composition238.py','--old',ROOT/'reference/boundary239_old.tm',
        '--new',ROOT/'machines/zfc_composed238_old.tm','--output',out/'local238.json'],out/'local238.json','PASS')
    run('bootstrap238',[ROOT/'verification/verify_bootstrap238.py','--canonical',ROOT/'machines/zfc_composed238.tm',
        '--inherited',ROOT/'machines/zfc_composed238_old.tm','--output',out/'bootstrap238.json'],out/'bootstrap238.json','EXACT_WHOLE_TAPE_SPARSE_DENSE_BOOTSTRAP_PASS')
    ks=run('ks_obstruction',[ROOT/'formalism/check_ks_obstruction.py','--output',out/'ks_obstruction.json'],
        out/'ks_obstruction.json','All declared finite obligations passed.')
    assert ks['total_cases']==11690 and ks['kernel_checked'] is False
    # Binding the different fresh proof obligations is essential: source identity
    # and runtime statements must concern exactly the same leaf array and table.
    assert (ROOT/'source/boundary224_sites.json').read_bytes()==(ROOT/'machines/sites_logical.json').read_bytes()
    runtime=json.loads((ROOT/'evidence/composed238_runtime.json').read_text())
    assert runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS' and runtime['cases']==8386
    assert runtime['table_sha256']==sha(ROOT/'machines/zfc_composed238_old.tm')
    assert runtime['sites_sha256']==sha(ROOT/'machines/sites_logical.json')
    assert runtime['checker_sha256']==sha(ROOT/'verification/check_literal_runtime.py')
    assert runtime['engine_sha256']==sha(ROOT/'verification/symbolic_runtime.py')
    assert runtime['helper_sha256']==sha(ROOT/'verification/independent_runtime.py')
    assert len(runtime['directly_used_rows'])==476 and runtime['minimum_actual_steps']==13
    if not args.quick:
        fresh=run('runtime238',[ROOT/'verification/check_literal_runtime.py','--table',ROOT/'machines/zfc_composed238_old.tm',
            '--sites',ROOT/'machines/sites_logical.json','--states',238,'--output',out/'runtime238.json'],out/'runtime238.json','UNIVERSAL_MATHEMATICAL_PASS')
        assert fresh['cases']==8386 and fresh['symbolic_steps']==2255513
        assert fresh['minimum_actual_steps']==13 and len(fresh['directly_used_rows'])==476
    if args.with_guard:
        run('selector_guard',[ROOT/'verification/prove_guard_boundary239.py','--checker',ROOT/'verification/symbolic_runtime.py',
            '--table',ROOT/'reference/boundary239_old.tm','--sites',ROOT/'machines/sites_logical.json',
            '--blank-prefix',ROOT/'reference/boundary239_blank_prefix.json','--output',out/'selector_guard.json'],
            out/'selector_guard.json','BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS')
    report={'status':'QUICK_REPLAY_PASS' if args.quick else 'FULL_238_MATHEMATICAL_REPLAY_PASS',
            'runtime_replayed':not args.quick,'selector_guard_replayed':args.with_guard,
            'kernel_endpoint_rebuilt':False,'inherited_calibration_rebuilt':False,
            'canonical_table_sha256':sha(ROOT/'machines/zfc_composed238.tm'),
            'jobs':jobs,'seconds':time.monotonic()-began}
    (out/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='jobs'},indent=2))

if __name__=='__main__': main()
