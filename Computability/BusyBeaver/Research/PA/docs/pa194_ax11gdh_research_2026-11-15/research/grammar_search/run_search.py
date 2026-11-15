#!/usr/bin/env python3
"""Compile and repeat one time-limited grammar search using only bundled inputs."""
from pathlib import Path
import argparse,json,subprocess
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__);p.add_argument('case',choices=[x['name']for x in json.loads((HERE/'cases.json').read_text())]);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=float);a=p.parse_args()
x=next(x for x in json.loads((HERE/'cases.json').read_text())if x['name']==a.case);src=HERE/a.case;a.output.mkdir(parents=True,exist_ok=True);exe=a.output.resolve()/'search'
subprocess.run(['g++','-O3','-std=c++17',str(src/'search.cpp'),'-o',str(exe)],check=True)
seconds=x['seconds']if a.seconds is None else a.seconds
with(a.output/'search.log').open('w')as log:subprocess.run([str(exe),str(src/'templates.txt'),str(src/'leaf_attrs.txt'),str(a.output/'run'),str(seconds),str(x['seed'])],stdout=log,check=True)
print((a.output/'search.log').read_text().splitlines()[-1])
