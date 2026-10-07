#!/usr/bin/env python3
"""Replay Report185 exact finite checks in normal and optimized Python.

The default needs only the standard library. --optional-numerics additionally
runs all bounded floating-point diagnostics, requiring mpmath, NumPy and SciPy.
Output always goes to a new directory outside the immutable source package.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify_manifest as manifest
import verify_frozen_sources
import verify_diagnostic_provenance
ROOT=Path(__file__).absolute().parent
SCRIPTS=('code/verify_exact.py','code/test_exact_guards.py','code/test_reproduction_guards.py')
REFERENCE='certificates/exact_checks.json'

def require(condition,message):
    if not condition:
        raise ArithmeticError(message)

def run_script(root,name,destination,optimized=False,args=(),optional=False):
    flags=['-I','-B'] if optional else ['-I','-S','-B']
    if optimized: flags.append('-O')
    bootstrap=('import runpy,sys; from pathlib import Path; script=sys.argv.pop(1); '
               'sys.path.insert(0,str(Path(script).parent)); sys.argv[0]=script; '
               'runpy.run_path(script,run_name="__main__")')
    command=[sys.executable,*flags,'-c',bootstrap,str(root/name),*map(str,args)]
    env={'PATH':os.environ.get('PATH',os.defpath),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8',
         'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
    process=subprocess.run(command,cwd=destination,env=env,capture_output=True,text=True,
                           timeout=1800 if optional else 900,shell=False)
    require(process.returncode==0,name+' failed:\n'+(process.stdout+process.stderr)[-12000:])
    result=manifest.load_json(process.stdout)
    require(isinstance(result,dict) and result.get('status')=='PASS',name+' did not return a PASS object')
    return result

def validate_output(root,output_dir):
    output_dir=Path(output_dir).absolute()
    require('..' not in output_dir.parts,'unsafe output directory')
    manifest.check_directory(output_dir.parent)
    require(not os.path.lexists(output_dir),'reproduction output already exists')
    require(not output_dir.resolve().is_relative_to(root.resolve()),'output must be outside source package')
    return output_dir

def run(root,output_dir,include_numerics=False):
    root=manifest.check_directory(root)
    frozen=verify_frozen_sources.verify(root)
    diagnostic_provenance=verify_diagnostic_provenance.verify(root)
    if (root/manifest.MANIFEST).exists():
        manifest.verify(root)
    output_dir=validate_output(root,output_dir)
    output_dir.mkdir(exist_ok=False)
    results=[]
    reference=manifest.read_regular(root/REFERENCE)
    for mode,optimized in [('normal',False),('optimized',True)]:
        destination=output_dir/mode;destination.mkdir()
        checks={}
        for name in SCRIPTS:
            args=['--output','exact_checks.json'] if name=='code/verify_exact.py' else []
            checks[name]=run_script(root,name,destination,optimized,args)
        require({p.name for p in destination.iterdir()}=={'exact_checks.json'},mode+' output inventory differs')
        require(manifest.read_regular(destination/'exact_checks.json')==reference,mode+' exact receipt differs')
        results.append(checks)
    require(results[0]==results[1],'normal and optimized checks disagree')
    result={'status':'PASS','standard_library_only_mandatory':True,
            'normal_and_optimized_identical':True,'exact_receipt_sha256':hashlib.sha256(reference).hexdigest(),
            'exact_checks':results[0]['code/verify_exact.py'],
            'exact_guard_tests':results[0]['code/test_exact_guards.py'],
            'reproduction_guard_tests':results[0]['code/test_reproduction_guards.py'],
            'frozen_sources':frozen,'diagnostic_provenance':diagnostic_provenance,
            'optional_numerics':{'run':False,'certified':False},
            'network_required':False}
    if include_numerics:
        receipt=run_script(root,'optional/run_all.py',output_dir,optional=True)
        with (output_dir/'optional_numerics.json').open('x',encoding='utf-8') as stream:
            stream.write(json.dumps(receipt,sort_keys=True,indent=2,allow_nan=False)+'\n')
        result['optional_numerics']={'run':True,'certified':False,'receipt':receipt}
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,help='new directory outside source; parent must exist')
    parser.add_argument('--optional-numerics',action='store_true')
    args=parser.parse_args()
    try:
        if args.output_dir is not None:
            result=run(ROOT,args.output_dir,args.optional_numerics)
        else:
            with tempfile.TemporaryDirectory(prefix='report185-replay-') as temporary:
                result=run(ROOT,Path(temporary)/'results',args.optional_numerics)
        print(json.dumps(result,sort_keys=True,indent=2,allow_nan=False))
    except (ArithmeticError,ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0

if __name__=='__main__':
    sys.exit(main())
