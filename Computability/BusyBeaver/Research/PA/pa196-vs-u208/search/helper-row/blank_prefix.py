#!/usr/bin/env python3
"""Finite blank-run simulation check for the PA196 {45,160} helper fold."""
from __future__ import annotations
import argparse
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('helper',HERE/'replay.py')
helper=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
require=helper.require

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--steps',type=int,default=1000000)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();require(args.steps>=0,'negative step bound')
    fold=helper.load_fold();table,digest=fold.read_table(fold.DEFAULT_TABLE)
    with tempfile.TemporaryDirectory(prefix='pa196-blank-prefix-') as directory:
        temp=Path(directory);binary=temp/'sim';source=temp/'table.txt'
        source.write_text(helper.table_text(table),encoding='ascii')
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',str(HERE/'blank_prefix.cpp'),'-o',str(binary)],check=True)
        words=subprocess.run([str(binary),str(source),str(args.steps)],check=True,text=True,capture_output=True).stdout.split()
    require('histogram' in words,'missing block histogram')
    split=words.index('histogram');keys=words[:split:2];values=words[1:split:2]
    expected_keys=['parent_steps','child_steps','parent_state','parent_head','parent_ones','visits_45','visits_160','visits_184']
    require(keys==expected_keys,f'unexpected simulator output: {words}')
    result=dict(zip(keys,map(int,values)))
    result['block_length_counts']={k:int(v) for k,v in (w.split(':') for w in words[split+1:])}
    result.update({'pa196_table_sha256':digest,'max_block_steps':512,'drop':45,'keep':160,
                   'patch_state':184,'patch_read':1,'patch':[1,'L',75],
                   'finite_prefix_only':True})
    output=json.dumps(result,indent=2,sort_keys=True)+'\n';print(output,end='')
    if args.output:args.output.write_text(output)

if __name__=='__main__':main()
