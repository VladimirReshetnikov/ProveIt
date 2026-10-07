#!/usr/bin/env python3
"""Replay exact algebra, rational tail inequalities and corruption guards offline.

Standard library only; normal and -O byte outputs must match fixed certificates.
Optional mpmath and SymPy diagnostics are never silently run by this command.
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
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import verify_manifest as manifest
import verify_source_data

SCRIPTS = {
    'formal_coefficients.json':'code/exact_coefficients.py',
    'positive_tails.json':'code/positive_tail.py',
    'mathematical_guards.json':'code/test_mathematical_guards.py',
}


def need(condition,message):
    if not condition:
        raise ArithmeticError(message)


def canonical(value):
    return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode('utf-8')


def run_script(root,script,optimized):
    bootstrap=('import runpy,sys; from pathlib import Path; script=sys.argv.pop(1); '
               'sys.path.insert(0,str(Path(script).parent)); sys.argv=[script]; '
               'runpy.run_path(script,run_name="__main__")')
    command=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])
    command+=['-c',bootstrap,str(root/script)]
    env={'PATH':os.defpath,'LANG':'C.UTF-8','LC_ALL':'C.UTF-8',
         'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
    result=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,
                          timeout=900,shell=False)
    need(result.returncode==0,script+' failed:\n'+(result.stdout+result.stderr)[-12000:])
    parsed=manifest.load_json(result.stdout)
    need(isinstance(parsed,dict) and parsed.get('status')=='PASS',
         'script must return a PASS object: '+script)
    return result.stdout.encode('utf-8')


def run(root,output):
    root=manifest.check_directory(root)
    if os.path.lexists(root/manifest.MANIFEST):
        manifest.verify(root)
    provenance=verify_source_data.verify(root)
    output=Path(output).absolute()
    need('..' not in output.parts,'unsafe reproduction output')
    manifest.check_directory(output.parent)
    need(not os.path.lexists(output),'reproduction output already exists')
    need(not output.resolve().is_relative_to(root.resolve()),'output must be outside package')
    with tempfile.TemporaryDirectory(prefix='report187-replay-',dir=output.parent) as temporary:
        work=Path(temporary)
        for mode,optimized in [('normal',False),('optimized',True)]:
            destination=work/mode
            destination.mkdir()
            for filename,script in SCRIPTS.items():
                content=run_script(root,script,optimized)
                reference=manifest.read_regular(root/'certificates'/filename)
                need(content==reference,mode+' output differs from reference: '+filename)
                with (destination/filename).open('xb') as stream:
                    stream.write(content)
        hashes={filename:hashlib.sha256(manifest.read_regular(work/'normal'/filename)).hexdigest()
                for filename in sorted(SCRIPTS)}
        result={'status':'PASS','standard_library_only':True,
                'normal_and_optimized_byte_identical_to_reference':True,
                'formal_order':6,'formal_modes':[1,2],
                'exact_positive_tail_cases':34,'exact_positive_tail_threshold':'1/10^35',
                'attributed_oeis_prefix_terms':35,
                'reference_file_count':len(SCRIPTS),'reference_sha256':hashes,
                'source_data':provenance,'optional_diagnostics_run':False,
                'floating_floor_evaluations_interval_certified':False,
                'scope':'Exact finite algebra and rational inequalities; analytic proof is in Report187'}
        output.mkdir(exist_ok=False)
        for mode in ('normal','optimized'):
            (output/mode).mkdir()
            for filename in SCRIPTS:
                with (output/mode/filename).open('xb') as stream:
                    stream.write(manifest.read_regular(work/mode/filename))
        with (output/'RESULT.json').open('xb') as stream:
            stream.write(canonical(result))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,help='new directory outside package; parent must exist')
    args=parser.parse_args()
    try:
        if args.output_dir is None:
            with tempfile.TemporaryDirectory(prefix='gamma-sampling-reproduce-') as temporary:
                result=run(ROOT,Path(temporary)/'results')
        else:
            result=run(ROOT,args.output_dir)
        print(json.dumps(result,sort_keys=True,indent=2))
    except (ArithmeticError,ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
