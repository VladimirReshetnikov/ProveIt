#!/usr/bin/env python3
"""Exact finite blank-start reachability of the pinned PA196 seed frame."""
import argparse,json,hashlib,time,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE/'runtime'
sys.path.insert(0,str(BASE));import independent_runtime as r

def step(table,q,h,bits):
    w,d,nxt=table[q,int(h in bits)]
    if w:bits.add(h)
    else:bits.discard(h)
    return nxt,h+d

def main():
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--bound',type=int,default=2000000)
    a=p.parse_args();old=r.table(HERE.parent/'data/pa196.native.tm');new=r.table(a.machine)
    bits=set();q=74;h=0
    for i in range(58154):q,h=step(old,q,h,bits)
    assert q==84 and h==-2 and len(bits)==66
    target=(q,h,bits.copy());q=74;h=0;bits=set();first=None;oq=74;oh=0;obits=set()
    start=time.monotonic();roots=0;status='NOT_REACHED_WITHIN_BOUND'
    for i in range(1,a.bound+1):
        if q==254:status='HALTED_BEFORE_SEED';break
        q,h=step(new,q,h,bits)
        if first is None:
            if oq==254:first=i
            else:
                oq,oh=step(old,oq,oh,obits)
                if (q,h,bits)!=(oq,oh,obits):first=i
        if q==84:
            roots+=1
            if (q,h,bits)==target:status='EXACT_BLANK_STARTUP_PASS';break
    report=dict(status=status,machine=str(a.machine),machine_sha256=hashlib.sha256(a.machine.read_bytes()).hexdigest(),
                baseline_native_sha256=hashlib.sha256((HERE.parent/'data/pa196.native.tm').read_bytes()).hexdigest(),
                baseline_seed_steps=58154,steps=i,root_visits=roots,first_literal_divergence=first,
                final_state=q,final_head=h,final_ones=sorted(bits),target_state=target[0],target_head=target[1],
                target_ones=sorted(target[2]),seconds=time.monotonic()-start,
                scope='Exact finite simulation of a literal binary one-tape table on the all-zero two-way-infinite tape; no bounded nonhalting conclusion.')
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if not k.endswith('_ones')},indent=2))
    if status != 'EXACT_BLANK_STARTUP_PASS': raise SystemExit(1)

if __name__=='__main__':main()
