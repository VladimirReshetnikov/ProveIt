#!/usr/bin/env python3
"""Run delivered tests, finite audits and paired local timings (standard library)."""
from pathlib import Path
import argparse
import subprocess
import sys
from experiments.audit import run as audit
from experiments.benchmark import run as benchmark


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',default='results-rerun')
    parser.add_argument('--skip-benchmark',action='store_true')
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    output=Path(args.output_dir).resolve();output.mkdir(parents=True,exist_ok=True)
    result=subprocess.run([sys.executable,'-m','unittest','discover','-s','tests','-v'],
                          cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (output/'unittest.txt').write_text(result.stdout)
    print(result.stdout,end='')
    if result.returncode: return result.returncode
    audit(output/'audit.json')
    if not args.skip_benchmark: benchmark(output)
    print('Evidence written to',output)
    return 0


if __name__=='__main__': raise SystemExit(main())
