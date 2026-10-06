#!/usr/bin/env python3
"""Offline immutable replay: exact checks, mutation tests, PDF rebuild and ZIP roundtrip.
Python 3.10+, pdfTeX and the standard TeX packages in report122.tex are required.
All results and work products are outside the delivered reader tree.
"""
import sys
sys.dont_write_bytecode=True
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile
import zipfile
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise RuntimeError(message)

def run(root,script,*args,optimize=False,timeout=600,cwd=None):
    command=[sys.executable,'-B']+(['-O'] if optimize else [])+[str(root/script),*map(str,args)]
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    cp=subprocess.run(command,cwd=cwd or root,env=env,capture_output=True,timeout=timeout)
    require(cp.returncode==0, 'REPLAY_FAILED '+script+': '+(cp.stdout+cp.stderr).decode(errors='replace'))
    return cp.stdout

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--skip-pdf',action='store_true',help='exact checks and ZIP roundtrip only; omit PDF rebuilds')
    args=parser.parse_args()
    if args.output:
        require(not args.output.resolve().is_relative_to(ROOT),'Output must be outside package')
    run(ROOT,'integrity.py')
    expected=(ROOT/'data/verification_results.json').read_bytes()
    original_pdf=(ROOT/'report122.pdf').read_bytes()
    with tempfile.TemporaryDirectory(prefix='report122-replay-') as td:
        work=Path(td)
        normal=work/'normal.json';optimized=work/'optimized.json';negative=work/'negative.json'
        run(ROOT,'checks/verify.py','--output',normal)
        run(ROOT,'checks/verify.py','--output',optimized,optimize=True)
        require(normal.read_bytes()==optimized.read_bytes()==expected,'CHECKER_BYTE_MISMATCH')
        run(ROOT,'checks/negative_tests.py','--output',negative,timeout=1800)
        require(negative.read_bytes()==(ROOT/'data/negative_results.json').read_bytes(),'NEGATIVE_BYTE_MISMATCH')
        outer=json.loads(run(ROOT,'test_integrity.py'))
        # Re-run the original auxiliary scripts in a disposable working directory.
        auxiliary=work/'auxiliary';auxiliary.mkdir()
        for name in ('verify_model.py','verify_orbit.py','certify.py','certify_corrections.py','global_bounds.py'):
            result=run(ROOT,'scripts/'+name,cwd=auxiliary)
            (auxiliary/(name+'.txt')).write_bytes(result)
        require((auxiliary/'a279558_n0_150.txt').read_bytes()==(ROOT/'data/a279558_n0_150.txt').read_bytes(),'AUXILIARY_SEQUENCE_MISMATCH')
        require((auxiliary/'certify.py.txt').read_bytes()==(ROOT/'data/certificate_output.txt').read_bytes(),'AUXILIARY_AMPLITUDE_MISMATCH')
        require((auxiliary/'certify_corrections.py.txt').read_bytes()==(ROOT/'data/correction_output.txt').read_bytes(),'AUXILIARY_CORRECTION_MISMATCH')
        if not args.skip_pdf:
            rebuilt=work/'rebuilt.pdf'
            run(ROOT,'build.py','--output',rebuilt,timeout=600)
            require(rebuilt.read_bytes()==original_pdf,'DELIVERED_PDF_REBUILD_MISMATCH')
        first=work/'first.zip';run(ROOT,'repack.py',first)
        with zipfile.ZipFile(first) as archive:
            for member in archive.infolist():
                rel=Path(member.filename);parts=rel.parts
                require(parts and parts[0]=='report122' and '..' not in parts and not rel.is_absolute(),'UNSAFE_ZIP_MEMBER')
            archive.extractall(work/'extracted')
        copy=work/'extracted/report122'
        run(copy,'integrity.py')
        for opt,label in [(False,'extracted'),(True,'extracted-optimized')]:
            dest=work/(label+'.json');run(copy,'checks/verify.py','--output',dest,optimize=opt)
            require(dest.read_bytes()==expected,'EXTRACTED_CHECKER_MISMATCH')
        if not args.skip_pdf:
            rebuilt=work/'extracted-rebuilt.pdf'
            run(copy,'build.py','--output',rebuilt,timeout=600)
            require(rebuilt.read_bytes()==original_pdf,'EXTRACTED_PDF_REBUILD_MISMATCH')
        run(copy,'integrity.py')
        second=work/'second.zip';run(copy,'repack.py',second)
        require(first.read_bytes()==second.read_bytes(),'ZIP_REPACK_BYTE_MISMATCH')
        result={'status':'PASS','normal_optimized_reference_bytes_equal':True,
                'independent_negative_tests':json.loads(negative.read_text()),
                'outer_inventory_negative_tests':outer,
                'auxiliary_reruns_match':True,
                'two_clean_pdf_builds_match':not args.skip_pdf,
                'fresh_extraction_normal_and_optimized_pass':True,
                'fresh_extraction_two_clean_pdf_builds_match':not args.skip_pdf,
                'fresh_repack_bytes_equal':True,
                'pdf_sha256':sha256(original_pdf).hexdigest(),
                'zip_sha256':sha256(first.read_bytes()).hexdigest(),
                'checker_output_sha256':sha256(expected).hexdigest()}
    run(ROOT,'integrity.py')
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(encoded)
    print(encoded,end='')

if __name__=='__main__':main()
