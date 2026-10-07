#!/usr/bin/env python3
"""Replay exact proofs/checks using only Python's standard library, normal and -O.

All output is written to a new directory outside the package. Optional floating
and SymPy diagnostics are separate commands and are never interval proofs.
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
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import verify_manifest as manifest
import verify_source_data

SCRIPTS={
    'common_truncations.json':'code/check_common_truncations.py',
    'amplitude_certificate.json':'code/certify_amplitudes.py',
    'exact_checks.json':'code/check_exact.py',
    'formal_coefficients.json':'code/formal_series.py',
    'positive_sum_audit.json':'code/audit_positive_sum.py',
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
    env={'PATH':os.defpath,'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
    result=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,timeout=900,shell=False)
    need(result.returncode==0,script+' failed:\n'+(result.stdout+result.stderr)[-12000:])
    parsed=manifest.load_json(result.stdout)
    need(isinstance(parsed,dict),'script result must be an object: '+script)
    if script!='code/certify_amplitudes.py':need(parsed.get('status')=='PASS','script did not report PASS: '+script)
    return result.stdout.encode('utf-8')


def run(root,output):
    root=manifest.check_directory(root)
    # Extracted releases are fully verified, not merely the source data.
    if os.path.lexists(root/manifest.MANIFEST):manifest.verify(root)
    provenance=verify_source_data.verify(root)
    output=Path(output).absolute()
    need('..' not in output.parts,'unsafe reproduction output')
    manifest.check_directory(output.parent)
    need(not os.path.lexists(output),'reproduction output already exists')
    need(not output.resolve().is_relative_to(root.resolve()),'output must be outside package')
    # Finish checks in isolated temporary storage before publishing a new directory.
    with tempfile.TemporaryDirectory(prefix='report186-replay-',dir=output.parent) as temporary:
        work=Path(temporary)
        for mode,optimized in [('normal',False),('optimized',True)]:
            destination=work/mode;destination.mkdir()
            for filename,script in SCRIPTS.items():
                content=run_script(root,script,optimized)
                reference=manifest.read_regular(root/'certificates'/filename)
                need(content==reference,mode+' output differs from reference: '+filename)
                with (destination/filename).open('xb') as stream:stream.write(content)
        truncations=manifest.load_json(manifest.read_regular(work/'normal/common_truncations.json'))
        common_places=min(v['rational_interval_common_truncated_places'] for seq in truncations['sequences'].values() for v in seq.values())
        need(common_places==69,'common truncation certificate did not verify 69 places')
        hashes={filename:hashlib.sha256(manifest.read_regular(work/'normal'/filename)).hexdigest() for filename in sorted(SCRIPTS)}
        result={'status':'PASS','standard_library_only':True,
                'normal_and_optimized_byte_identical_to_reference':True,
                'N':10000,'official_bfile_terms_each':1000,
                'formal_forward_order':9,'independent_positive_sum_audit':True,
                'reference_file_count':len(SCRIPTS),'reference_sha256':hashes,
                'source_data':provenance,'optional_diagnostics_run':False,
                'published_endpoint_places':70,'common_truncated_decimal_places_from_exact_rational_intervals':common_places,
                'common_truncation_certificate':'certificates/common_truncations.json',
                'displayed_ceiling_A_common_prefix_places':68}
        output.mkdir(exist_ok=False)
        for mode in ('normal','optimized'):
            (output/mode).mkdir()
            for filename in SCRIPTS:
                with (output/mode/filename).open('xb') as stream:stream.write(manifest.read_regular(work/mode/filename))
        with (output/'RESULT.json').open('xb') as stream:stream.write(canonical(result))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,help='new directory outside the package; parent must exist')
    args=parser.parse_args()
    try:
        if args.output_dir is None:
            with tempfile.TemporaryDirectory(prefix='rounded-mean-reproduce-') as temporary:
                result=run(ROOT,Path(temporary)/'results')
        else:result=run(ROOT,args.output_dir)
        print(json.dumps(result,sort_keys=True,indent=2))
    except (ArithmeticError,ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':sys.exit(main())
