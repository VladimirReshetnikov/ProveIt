#!/usr/bin/env python3
"""Run the exact or numerical replay suites and preserve their logs."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
SUITES={
    'exact':['translation_polynomials.py','verify_depth_projector.py','project_s6_depth.py'],
    'numeric':['verify_translation.py','verify_translation_extensions.py','verify_critical_sums.py'],
    'euler':['verify_transition.py'],
}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite',choices=['exact','numeric','euler','all'],default='exact')
    args=parser.parse_args()
    suites=SUITES if args.suite=='all' else {args.suite:SUITES[args.suite]}
    for suite,programs in suites.items():
        for program in programs:
            print(suite+': '+program,flush=True)
            run=subprocess.run([sys.executable,str(ROOT/'code'/program)],cwd=ROOT,
                               stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            (ROOT/'verification'/(Path(program).stem+'.log')).write_text(run.stdout)
            if run.returncode:
                print(run.stdout[-5000:])
                raise SystemExit(run.returncode)
            print('Completed with exit code 0.',flush=True)
    print('Requested replay suite completed. Numerical outputs remain diagnostics.')


if __name__=='__main__':main()
