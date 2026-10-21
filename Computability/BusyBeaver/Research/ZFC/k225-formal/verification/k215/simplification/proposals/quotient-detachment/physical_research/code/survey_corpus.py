#!/usr/bin/env python3
"""Portable reproduction of the scoped 21-table physical survey."""
from pathlib import Path
import argparse,subprocess,json,sys,hashlib
ROOT=Path(__file__).resolve().parent.parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--shared-helper',action='store_true');a=ap.parse_args();a.output.mkdir(exist_ok=False)
    corpus=[dict(filename='../k215.native.tm',repository_path='primary K215')]+json.loads((ROOT/'inputs/variant_index.json').read_text());results=[]
    tool='shared_helper_search.py'if a.shared_helper else'two_branch_fusions.py'
    for i,row in enumerate(corpus):
        p=(ROOT/'inputs/variants'/row['filename']).resolve()
        if 'sha256'in row:assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        output=a.output/f'{i:02d}.json'
        with(a.output/f'{i:02d}.log').open('w')as log:r=subprocess.run([sys.executable,str(ROOT/'code'/tool),str(p),'--output',str(output)],stdout=log,stderr=subprocess.STDOUT)
        if r.returncode:raise RuntimeError(f'Search failed for {p}')
        d=json.loads(output.read_text());d.pop('rows',None);results.append(dict(repository_path=row['repository_path'],**d));print(i,row['repository_path'],len(d['survivors']),flush=True)
    (a.output/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
