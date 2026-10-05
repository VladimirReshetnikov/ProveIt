#!/usr/bin/env python3
"""Run preserved mpmath scout programs in a NEW external output directory.

Numerical diagnostics only: no rigorous tail, rounding, or error certificate.
Unlike the core build, output includes nondeterministic wall-clock timings.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
import verify_manifest
SCRIPTS=('verify_nested_partitions.py','verify_marked.py','verify_maximum.py')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    out=args.output.absolute()
    verify_manifest.check_directory(out.parent)
    if os.path.lexists(out) or out.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError('output must be new and outside the package')
    with tempfile.TemporaryDirectory(prefix='report181-numerical-',dir=out.parent) as temporary:
        work=Path(temporary)
        for name in SCRIPTS:
            (work/name).write_bytes(verify_manifest.read_regular(ROOT/'optional/scout'/name))
        for name in SCRIPTS:
            result=subprocess.run([sys.executable,'-B',name],cwd=work,text=True,
                                  capture_output=True,shell=False,timeout=1800,
                                  env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
            (work/(name+'.log')).write_text(result.stdout+result.stderr)
            if result.returncode:
                raise RuntimeError(name+' failed: '+result.stderr[-4000:])
        out.mkdir(exist_ok=False)
        for path in sorted(work.iterdir()):
            if path.is_file() and path.suffix in ('.json','.txt','.log'):
                with (out/path.name).open('xb') as stream:
                    stream.write(path.read_bytes())
    print('Numerical diagnostics written to '+str(out)+'; these are not proof certificates.')


if __name__=='__main__':
    main()
