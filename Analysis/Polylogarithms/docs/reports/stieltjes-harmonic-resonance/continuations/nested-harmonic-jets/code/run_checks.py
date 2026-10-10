#!/usr/bin/env python3
"""Replay the packaged checks; a failed child aborts the run."""
from __future__ import annotations
import argparse,subprocess,sys
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true',help='Run exact algebra and higher-jet coefficient checks only')
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    scripts=['verify_exact.py','verify_higher_jets.py']
    if not args.quick:scripts+=['verify_numeric.py','verify_cyclotomic.py']
    for name in scripts:
        print(f'\n=== {name} ===',flush=True)
        subprocess.run([sys.executable,str(root/'code'/name)],cwd=root,check=True)
    print('\nAll requested suites passed. Numerical suites are not interval certificates.')
if __name__=='__main__':main()
