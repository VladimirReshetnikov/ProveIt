#!/usr/bin/env python3
"""Replay mandatory exact checks in normal/-O Python; SymPy is opt-in only."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
import verify_manifest as manifest


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()


def snapshot(root):
    files, directories = manifest.scan(root)
    return ({name:hashlib.sha256(manifest.read_regular(path)).hexdigest()
             for name,path in sorted(files.items())}, directories)


def run_process(command, root, env):
    result = subprocess.run(command, cwd=root, env=env, capture_output=True,
                            timeout=900, shell=False)
    manifest.need(result.returncode == 0, 'replay command failed:\n'+
                  (result.stdout+result.stderr)[-12000:].decode(errors='replace'))
    return result.stdout


def run(root, output, symbolic=False):
    import build
    root = manifest.check_directory(root)
    output = manifest.fresh_output(output, root)
    build.validate_source(root)
    before = snapshot(root)
    env = {'PATH':os.environ.get('PATH',os.defpath), 'LC_ALL':'C.UTF-8',
           'TZ':'UTC', 'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
    with tempfile.TemporaryDirectory(prefix='report195-replay-',dir=output.parent) as temporary:
        work = Path(temporary)
        results = []
        for mode, optimized in [('normal',False),('optimized',True)]:
            flags = ['-I','-S','-B'] + (['-O'] if optimized else [])
            stdout = run_process([sys.executable,*flags,str(root/'code/check_exact.py'),
                                  '--output-dir',str(work/mode)],root,env)
            files, directories = manifest.scan(work/mode)
            manifest.need(set(files)=={'exact_checks.json','exact_terms.txt'} and not directories,
                          'unexpected exact-check output inventory')
            payload = {name:manifest.read_regular(path) for name,path in files.items()}
            receipt = manifest.load_json(payload['exact_checks.json'])
            manifest.need(receipt['status']=='PASS' and receipt['arithmetic']=='integer and Fraction only',
                          'exact-check declaration mismatch')
            manifest.need(stdout==payload['exact_checks.json']==canonical(receipt),
                          'exact-check stdout/receipt mismatch')
            terms = payload['exact_terms.txt']
            manifest.need(receipt['exact_terms_sha256']==hashlib.sha256(terms).hexdigest()
                          and type(receipt['exact_terms_bytes']) is int
                          and receipt['exact_terms_bytes']==len(terms),'exact terms digest mismatch')
            results.append(payload)
        manifest.need(results[0]==results[1], 'normal/-O exact replay bytes differ')
        symbolic_payload = {}
        if symbolic:
            tasks=[('independent_wick_check.py','symbolic_check.txt',b'exact symbolic identity checks: PASS\n'),
                   ('second_wick_check.py','second_symbolic_check.txt',b'exact second symbolic identity checks: PASS\n')]
            for script,name,sentinel in tasks:
                symbols=[]
                for optimized in (False,True):
                    flags=['-I','-B']+(['-O'] if optimized else [])
                    symbols.append(run_process([sys.executable,*flags,str(root/'code'/script)],root,env))
                manifest.need(symbols[0]==symbols[1] and sentinel in symbols[0],
                              'symbolic check failed or normal/-O output differs: '+script)
                symbolic_payload[name]=symbols[0]
        result = {'status':'PASS','mandatory_standard_library_only':True,
                  'normal_and_optimized_byte_identical':True,'maximum_n':1500,
                  'symbolic_requested':symbolic,'floating_diagnostics_run':False,
                  'files':{name:{'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
                           for name,data in sorted(results[0].items())},
                  'scope':'Exact finite checks; analytic asymptotic proof is in Report195.tex'}
        if symbolic_payload:
            result['symbolic']={'normal_and_optimized_byte_identical':True,
                'files':{name:{'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
                         for name,data in sorted(symbolic_payload.items())}}
        manifest.need(snapshot(root)==before,'source changed during replay')
        output.mkdir(exist_ok=False)
        for mode, payload in zip(('normal','optimized'),results):
            (output/mode).mkdir()
            for name,data in payload.items():
                with (output/mode/name).open('xb') as stream:
                    stream.write(data)
        for name,data in sorted(symbolic_payload.items()):
            with (output/name).open('xb') as stream:
                stream.write(data)
        with (output/'RESULT.json').open('xb') as stream:
            stream.write(canonical(result))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--symbolic',action='store_true',help='also regenerate independent SymPy identities')
    args=parser.parse_args()
    try:
        if args.output_dir is None:
            with tempfile.TemporaryDirectory(prefix='report195-reproduce-') as temporary:
                result=run(ROOT,Path(temporary)/'result',args.symbolic)
        else:
            result=run(ROOT,args.output_dir,args.symbolic)
        sys.stdout.buffer.write(canonical(result))
    except (ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
