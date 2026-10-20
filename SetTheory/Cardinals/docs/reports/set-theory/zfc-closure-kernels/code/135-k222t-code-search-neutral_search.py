#!/usr/bin/env python3
"""Portable neutral-rewrite-then-fold exploration; Python standard library.

The C++ kernel first rederives all accepted neutral actions for the supplied
table, then resynthesizes contextual folds after each individual rewrite.
This exploratory search is optional and is not part of the K222 proof replay.
Any reported smaller table still needs an independent positive certificate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time

def read_table(path):
    table={};start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            if start is not None:raise ValueError('Duplicate start declaration')
            start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        if (q,b) in table or b not in(0,1) or w not in(0,1) or d not in('L','R'):
            raise ValueError('Malformed table row')
        table[q,b]=w,1 if d=='R'else-1,z
    states={q for q,b in table}
    if start!=0 or 254 in states or set(table)!={(q,b)for q in states for b in(0,1)}:
        raise ValueError('Expected a complete K-labelled table with start0 and halt254')
    if {z for w,d,z in table.values()}-states!={254}:
        raise ValueError('Unexpected target state')
    return table

def emit(table):
    return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
        for(q,b),(w,d,z)in sorted(table.items()))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--executable',type=Path,default=Path(__file__).with_name('fold_search'))
    ap.add_argument('--block-limit',type=int,default=24)
    args=ap.parse_args()
    table_path=args.table.resolve();output=args.output_dir.resolve();executable=args.executable.resolve()
    if not 1<=args.block_limit<=128:raise ValueError('Block limit must lie in1..128')
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise ValueError('Output directory must be absent or empty')
    if not executable.is_file():raise ValueError('Compile fold_search.cpp first or pass --executable')
    base=read_table(table_path);output.mkdir(parents=True,exist_ok=True)
    def run(path,neutral=False):
        command=[str(executable),str(path),str(args.block_limit)]+(['neutral']if neutral else[])
        result=subprocess.run(command,text=True,capture_output=True,cwd=output)
        if result.returncode:raise RuntimeError(result.stderr)
        return result
    initial=run(table_path,True)
    (output/'neutral_actions.txt').write_text(initial.stdout)
    (output/'neutral_generation.log').write_text(initial.stderr)
    variants=[tuple(map(int,line.split()))for line in initial.stdout.splitlines()]
    # This order matches the measured original experiment for the main table.
    focus={118,159,155,153,166,300,301,304,305,306}
    variants.sort(key=lambda row:(row[0]not in focus,row[0]))
    begun=time.monotonic();success=[];logs=[]
    for index,change in enumerate(variants):
        q,b,w,d,z=change;changed=dict(base);changed[q,b]=w,d,z
        current=output/'neutral_current.k.tm';current.write_text(emit(changed))
        result=run(current);logs.append({'index':index,'neutral':change,'screen':result.stderr.strip()})
        for line in result.stdout.splitlines():
            kind,keep,drop,w0,d0,z0,w1,d1,z1=line.split()
            if kind!='FOLD':raise ValueError('Unexpected search output')
            keep,drop,w0,d0,z0,w1,d1,z1=map(int,(keep,drop,w0,d0,z0,w1,d1,z1))
            phi=lambda state:keep if state==drop else state
            new={(state,bit):(write,direction,phi(target))
                 for(state,bit),(write,direction,target)in changed.items()if state!=drop}
            new[keep,0]=w0,d0,phi(z0);new[keep,1]=w1,d1,phi(z1)
            filename=f'potential{len(new)//2}-{len(success)}.k.tm'
            (output/filename).write_text(emit(new))
            record={'neutral':change,'fold':line,'states':len(new)//2,'table':filename}
            success.append(record);print('SEARCH_SURVIVOR',json.dumps(record),flush=True)
        if index%25==0:print('screened',index+1,'/',len(variants),flush=True)
    summary={'status':'SCOPED_SEARCH_COMPLETE','input_sha256':hashlib.sha256(table_path.read_bytes()).hexdigest(),
             'neutral_variants':len(variants),'survivors':success,'block_limit':args.block_limit,
             'seconds':time.monotonic()-begun,'scope':'Known-cell radius6; existing-working-state first-action targets; nonstart state folds; no minimality claim.'}
    (output/'screens.json').write_text(json.dumps(logs,indent=2)+'\n')
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
