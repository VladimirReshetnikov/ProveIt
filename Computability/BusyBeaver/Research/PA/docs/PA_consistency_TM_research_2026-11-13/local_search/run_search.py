#!/usr/bin/env python3
"""Rebuild and rerun the bounded searches in a fresh output directory.

Default: all fourteen designated tables. --refined-baseline uses the supplied
2,219-window PA196 source invariant. --control exercises the same C++ code
on the four-state positive-control machine.
"""
import argparse, concurrent.futures, hashlib, importlib.util, json, subprocess
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent

def parse(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split()
        key=(int(q),int(b))
        if key in t:raise ValueError('Duplicate row')
        t[key]=(int(w),1 if d=='R' else -1,int(z))
    if set(t)!={(q,b)for q in range(196)for b in(0,1)}:
        raise ValueError('Not a complete196-state table')
    return t

def one(job):
    path,out,exe,refined=map(Path,job)
    out.mkdir()
    start=time.monotonic()
    source_sha=hashlib.sha256(path.read_bytes()).hexdigest()
    if refined.name!='NONE':
        contexts=refined.read_bytes()
        closure=None;mayhalt=None
    else:
        spec=importlib.util.spec_from_file_location('fold',HERE/'scan_local_folds.py')
        fold=importlib.util.module_from_spec(spec);spec.loader.exec_module(fold)
        c,mayhalt,closure=fold.blank_window_contexts(parse(path),6)
        contexts=''.join(f'{q} {b} {sum(t[i]<<(i+2)for i in range(-2,3))}\n'
                         for(q,b),windows in sorted(c.items())for t in windows).encode()
    cp=out/'contexts.txt';cp.write_bytes(contexts)
    tp=out/'machine.tm';tp.write_bytes(path.read_bytes())
    with(out/'counts.txt').open('w')as stdout,(out/'progress.log').open('w')as stderr:
        subprocess.run([str(exe),str(tp),str(cp),str(out/'candidates.txt'),'196'],
                       stdout=stdout,stderr=stderr,check=True)
    receipt={'name':path.stem,'input_sha256':source_sha,'radius':None if closure is None else 6,
             'closure_pairs':closure,'projected_contexts':len(contexts.splitlines()),
             'abstract_halt_reachable':mayhalt,'counts':(out/'counts.txt').read_text().strip(),
             'candidates':(out/'candidates.txt').read_text().splitlines(),
             'seconds':time.monotonic()-start}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    return receipt

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--workers',type=int,default=3)
    ap.add_argument('--refined-baseline',action='store_true')
    ap.add_argument('--control',action='store_true')
    args=ap.parse_args();out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    cpp=(HERE/'three_row_extension.cpp').read_text()
    if args.control:cpp=cpp.replace('constexpr int N=196;','constexpr int N=4;')
    src=out/'search.cpp';src.write_text(cpp)
    exe=out/'search'
    subprocess.run(['g++','-std=c++17','-O3',str(src),'-o',str(exe)],check=True)
    if args.control:
        with(out/'counts.txt').open('w')as stdout:
            subprocess.run([str(exe),str(HERE/'control.tm'),str(HERE/'control_contexts.txt'),
                            str(out/'candidates.txt'),'4'],stdout=stdout,check=True)
        print((out/'counts.txt').read_text(),end='')
        return
    if args.refined_baseline:
        paths=[HERE/'pa196_original.tm'];refined=HERE/'pa196_source_contexts.txt'
    else:
        paths=sorted((HERE.parent/'selected196_tables').glob('*.tm'));refined=Path('NONE')
    jobs=[(str(p),str(out/p.stem),str(exe),str(refined))for p in paths]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers)as pool:
        receipts=list(pool.map(one,jobs))
    (out/'summary.json').write_text(json.dumps(receipts,indent=2)+'\n')

if __name__=='__main__':main()
