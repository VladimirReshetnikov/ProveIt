#!/usr/bin/env python3
"""Compile and rerun the finite shared-helper search on its pinned table."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
TABLE_SHA='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
def require(x,msg):
    if not x:raise ValueError(msg)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path('fresh_receipt.json'))
    ap.add_argument('--general',action='store_true')
    args=ap.parse_args()
    source=ROOT/('search_general.cpp'if args.general else'search.cpp');table=ROOT/'inputs/pa196.tm'
    require(hashlib.sha256(table.read_bytes()).hexdigest()==TABLE_SHA,'Pinned reference-table hash mismatch')
    compiler=shutil.which('c++')or shutil.which('g++')
    require(compiler is not None,'A C++20 compiler is required')
    args.output=args.output.resolve();args.output.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='pa196_shared_helper_')as td:
        exe=Path(td)/'search'
        subprocess.run([compiler,'-std=c++20','-O3',str(source),'-o',str(exe)],check=True)
        subprocess.run([str(exe),str(table),str(args.output)],check=True)
    d=json.loads(args.output.read_text())
    expected={'working_states_reference':196,'eligible_pairs':14,'disjoint_pair_choices':88,
              'patches_tested':13660768,'helper_target_choices_each':197,
              'maximum_block_steps':64,'survivors':[]}
    if args.general:expected.update(patches_tested=218572288,helper_row_action_patterns=16)
    require(all(d.get(k)==v for k,v in expected.items()),'Recomputed search outcome differs')
    print(json.dumps({'status':'PASS','receipt':str(args.output),'scope':'Finite two-pair, one-helper family; no smaller TM found'},indent=2))

if __name__=='__main__':main()
