#!/usr/bin/env python3
"""Run the package without installing it or using the network."""
from __future__ import annotations
import argparse, os, subprocess, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def call(args,cwd=ROOT):
    env=os.environ.copy()
    env['PYTHONPATH']=str(ROOT/'src')+os.pathsep+env.get('PYTHONPATH','')
    subprocess.run(args,cwd=cwd,env=env,check=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['test','audit','benchmark','patches','ranks','example','pdf'])
    parser.add_argument('--out',help='Output JSON path for audit or benchmarks; default writes retained result path')
    args=parser.parse_args()
    if args.command=='test':
        call([sys.executable,'-m','unittest','discover','-s','tests','-v'])
    elif args.command=='pdf':
        call([sys.executable,'experiments/make_tables.py'])
        for _ in range(3):
            call(['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex'],ROOT/'paper')
    else:
        script={'audit':'experiments/audit.py','benchmark':'experiments/benchmark.py',
                'patches':'experiments/patch_benchmark.py','ranks':'experiments/group_rank.py',
                'example':'examples/demo.py'}[args.command]
        cmd=[sys.executable,script]
        if args.out:
            if args.command not in ('audit','benchmark','patches'):
                parser.error('--out is only supported for audit, benchmark, and patches')
            cmd.extend(['--out',args.out])
        call(cmd)

if __name__=='__main__':main()
