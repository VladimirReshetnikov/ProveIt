#!/usr/bin/env python3
"""Replay two bounded closed-fragment grammar searches; C++17 is required."""
import argparse,json,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=240);ap.add_argument('--output',type=pathlib.Path);args=ap.parse_args()
output=args.output or pathlib.Path(tempfile.mkdtemp(prefix='pa194-closed-fragments-'));output.mkdir(parents=True,exist_ok=True)
results=[]
for name,seed in [('run_copy',20261114),('run_phases',20261115)]:
 src=HERE/name;run=output/name;run.mkdir(parents=True,exist_ok=True);exe=run/'search'
 subprocess.run(['g++','-O3','-std=c++17',str(src/'search.cpp'),'-o',str(exe)],check=True)
 with (run/'search.log').open('w')as log:
  subprocess.run([str(exe),str(src/'expanded.txt'),str(src/'expanded_attrs.txt'),str(run/'result'),str(args.seconds),str(seed)],stdout=log,stderr=subprocess.STDOUT,check=True)
 text=(run/'search.log').read_text();m=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([0-9.]+)',text)
 assert m,text[-2000:]
 results.append(dict(run=name,proposals=int(m[1]),accepted=int(m[2]),hits_below_194=int(m[3]),best_effective_readers=int(m[4]),seconds=float(m[5]),output=str(run)))
print(json.dumps({'results':results,'scope':'Stochastic grammar fitness only. A candidate still needs full source, literal-tape, and startup verification; failure is not a lower bound.'},indent=2))
