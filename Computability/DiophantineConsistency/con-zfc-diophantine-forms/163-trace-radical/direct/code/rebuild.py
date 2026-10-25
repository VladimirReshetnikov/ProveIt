#!/usr/bin/env python3
"""Reconstruct selected new mathematical artifacts in a disposable copy."""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent.parent
def run(root,args):
    p=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=root,text=True,capture_output=True)
    if p.returncode:raise RuntimeError(p.stdout+'\n'+p.stderr)
def main():
    with tempfile.TemporaryDirectory(prefix='conzfc-quadratic-radical-') as td:
        work=Path(td)/'component';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        run(work,['code/build_self_power.py'])
        cases=[('self_power235','lineage/self_power/affine241/equation.json'),('self_power236','lineage/self_power/affine242/equation.json'),('shared_error234','inherited/shared_error/equations/equation240/equation.json')]
        count=0
        for name,source in cases:
            out=Path('equations')/name
            run(work,['code/radical_project.py',source,out])
            for fn in ['equation.json','expanded_polynomial.json','certificate.json','METRICS.json']:
                if (work/out/fn).read_bytes()!=(ROOT/out/fn).read_bytes():raise ValueError('rebuild mismatch '+str(out/fn))
                count+=1
        for original in (ROOT/'lineage/self_power').rglob('*.json'):
            relative=original.relative_to(ROOT)
            if original.read_bytes()!=(work/relative).read_bytes():raise ValueError('lineage mismatch '+str(relative))
            count+=1
        run(work,['code/verify.py'])
    print(json.dumps({'status':'PASS','byte_identical_mathematical_json_files':count,'original_files_unchanged':True},indent=2))
if __name__=='__main__':main()
