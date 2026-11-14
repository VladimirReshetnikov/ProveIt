#!/usr/bin/env python3
"""Bounded blank-startup regression; a timeout is not a nonhalting proof."""
from pathlib import Path
import argparse,hashlib,json,time
from check_pruned import HERE,load_table,verify_inputs,require

def step(table,q,h,ones):
    w,d,z=table[q,int(h in ones)]
    if w:ones.add(h)
    else:ones.discard(h)
    return z,h+d

def decode_candidate2(q,h,ones):
    if q!=84 or not ones or min(ones)!=h-1 or h not in ones:return None
    right=sorted(x for x in ones if x>=h)
    if len(right)<2 or right[1]<h+39:return None
    marker=right[1];at=marker+1;last=max(ones);values=[]
    while at<=last:
        if at in ones or at+1 not in ones:return None
        at+=1;begin=at
        while at in ones:at+=1
        values.append(at-begin-1)
    if len(values)<10:return None
    registers=[values[j]for j in(6,2,0,4,3,7,8,5,1)]
    if registers!=[2,0,0,0,0,0,0,0,0]:return None
    return {'marker_offset':marker-h,'registers':registers,'spares':values[9:]}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--steps',type=int,default=1000000);parser.add_argument('--output',type=Path,default=HERE/'startup_receipt.json');args=parser.parse_args()
    require(args.steps>=0,'Negative bound');verify_inputs()
    baseline=load_table(HERE/'data/pa196_baseline.native.tm');q=74;h=0;ones=set()
    for _ in range(58154):q,h=step(baseline,q,h,ones)
    require(q==84 and decode_candidate2(q,h,ones)is not None,'Published seed did not reproduce')
    goal={x-h for x in ones};table=load_table(HERE/'data/runtime_198.native.tm');q=74;h=0;ones=set();exact=None;decoded=None;halted=None;start=time.monotonic()
    for tick in range(args.steps+1):
        if q==84:
            if exact is None and {x-h for x in ones}==goal:exact=tick
            d=decode_candidate2(q,h,ones)
            if decoded is None and d is not None:decoded={'steps':tick,**d}
        if q==254:halted=tick;break
        if tick==args.steps:break
        q,h=step(table,q,h,ones)
    result={'status':'NOT_CALIBRATED_WITHIN_BOUND'if decoded is None else'CANDIDATE_FRAME_FOUND_REQUIRES_REVIEW','checked_steps':tick,'published_baseline_startup_steps':58154,'first_exact_published_seed':exact,'first_decoded_candidate2_frame':decoded,'halted_at':halted,'final_native_state':q,'final_head':h,'final_one_cell_count':len(ones),'elapsed_seconds':time.monotonic()-start,'table_sha256':hashlib.sha256((HERE/'data/runtime_198.native.tm').read_bytes()).hexdigest(),'accepted_blank_tape_con_pa_machine':False,'scope':'Literal bounded replay only. Failure to reach a calibrated frame within this bound does not prove that no such frame occurs later; runtime contracts alone do not authorize a Con(PA) claim from blank tape.'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
