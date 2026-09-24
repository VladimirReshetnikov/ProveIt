#!/usr/bin/env python3
"""Reproduce data tables and cross-check the two exact implementations."""
import argparse
import csv
import json
import platform
from pathlib import Path
from time import perf_counter
from a281434 import terms, a_modular, upper_bound, lower_bound

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)

def reference():
    start = perf_counter()
    values = list(terms(100))
    seconds = perf_counter()-start
    (DATA/'b281434.txt').write_text(''.join(f'{n} {v}\n' for n,v in enumerate(values)))
    (DATA/'b352697.txt').write_text(''.join(f'{n} {upper_bound(n)-v}\n' for n,v in enumerate(values) if n))
    env=dict(python=platform.python_version(),platform=platform.platform(),
             reference_prefix_100_seconds=seconds,modulus=1_000_000_007)
    try:
        import numpy
        env['numpy']=numpy.__version__
    except ImportError:
        env['numpy']=None
    env['implementation']=platform.python_implementation()
    env['timing_note']='Individual wall-clock runs; reference computes prefix 0..100, modular timings compute one target.'
    (DATA/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
    print('Reference prefix 0..100:',seconds,'seconds',flush=True)

def benchmarks(indices):
    old=DATA/'benchmarks.csv'
    rows=[]
    if old.exists():
        with old.open() as f:
            rows=list(csv.DictReader(f))
    holes_by_n={}
    if (DATA/'selected_holes.json').exists():
        holes_by_n=json.loads((DATA/'selected_holes.json').read_text())
    values={}
    if (DATA/'b281434.txt').exists():
        values=dict(tuple(map(int,line.split())) for line in (DATA/'b281434.txt').read_text().splitlines())
    for n in indices:
        start=perf_counter()
        value, holes, candidates=a_modular(n,details=True)
        seconds=perf_counter()-start
        if n in values:
            assert value==values[n]
        rows=[r for r in rows if int(r['n'])!=n]
        row=dict(n=n,a=value,upper_bound=upper_bound(n),lower_bound=lower_bound(n),
                 deficit=upper_bound(n)-value,modular_candidates=candidates,
                 seconds=round(seconds,6))
        rows.append(row)
        holes_by_n[str(n)]=holes
        print(row,flush=True)
        rows.sort(key=lambda r:int(r['n']))
        with old.open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(row))
            writer.writeheader();writer.writerows(rows)
        (DATA/'selected_holes.json').write_text(json.dumps(holes_by_n,indent=2)+'\n')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference',action='store_true')
    parser.add_argument('indices',type=int,nargs='*')
    args=parser.parse_args()
    if args.reference:reference()
    if args.indices:benchmarks(args.indices)
