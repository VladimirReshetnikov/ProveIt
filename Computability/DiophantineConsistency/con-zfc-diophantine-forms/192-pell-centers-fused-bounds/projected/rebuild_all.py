#!/usr/bin/env python3
"""Rebuild every new circuit in temporary memory and compare exact bytes."""
from pathlib import Path
import importlib.util,json,sys,tempfile,zipfile,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build,build_orientation_seed

def same(p,b):
    if p.read_bytes()!=b:raise ValueError('Rebuild mismatch: '+str(p))
def main():
    doc=build_orientation_seed.build(ROOT/'sources/joint209.json')
    same(ROOT/'sources/joint209_linear_orientation.json',(json.dumps(doc,sort_keys=True,indent=2)+'\n').encode())
    made=1
    with tempfile.TemporaryDirectory(prefix='conzfc-guard-rebuild-') as t:
        t=Path(t)
        with zipfile.ZipFile(ROOT/'sources/parent_archive.zip') as z:z.extractall(t)
        parent=t/'ConZFC_Direct_Integer_Elimination_2026-10-25'
        sys.path.insert(0,str(parent/'code'))
        import producer
        for p in (ROOT/'sources').glob('integer*_linear.json'):
            old=json.loads(p.with_name(p.name.replace('_linear.json','.json')).read_text())
            rebuilt=producer.build({'steps':old['elimination_steps']},ROOT/'sources/joint209_linear_orientation.json')
            same(p,build.canonical(rebuilt));made+=1
    for p in (ROOT/'equations').glob('integer*_degree*.json'):
        frozen=json.loads(p.read_text());rebuilt=build.build(ROOT/'sources'/frozen['parent_file'])
        same(p,build.canonical(rebuilt));made+=1
    print(json.dumps({'status':'pass','byte_exact_rebuilt_files':made,'source':'frozen immediate parent, linear orientation and reciprocal guard'},indent=2))
if __name__=='__main__':main()
