#!/usr/bin/env python3
"""Independent sparse and dense exact blank-start checks against the full frame."""
from pathlib import Path
from collections import Counter
import argparse,json,hashlib
from verify_runtime import parse,require

def expected():
    support={-6,176};pos=177
    for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
        pos+=1;support.update(range(pos,pos+value+1));pos+=value+1
    return support
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=1000000);a=ap.parse_args()
    t=parse(a.table);target=expected();require(len(target)==351,'Bad expected frame')
    q=h=0;ones=set();visits=Counter();minimum=maximum=0
    for steps in range(a.limit+1):
        if q==84 and h==-5 and ones==target:break
        require(steps<a.limit,'Exact frame not reached within startup proof budget')
        key=q,int(h in ones);visits[key]+=1;w,d,z=t[key]
        if w:ones.add(h)
        else:ones.discard(h)
        q,h=z,h+d;minimum=min(minimum,h);maximum=max(maximum,h)
    # A separately implemented bounded dense tape gives an independent literal replay.
    pad=32;offset=-minimum+pad;cells=bytearray(maximum-minimum+2*pad+1);state=0;head=offset
    for i in range(steps):
        require(0<=head<len(cells),'Dense bounds are insufficient')
        write,direction,next_state=t[state,cells[head]];cells[head]=write;head+=direction;state=next_state
    actual={i-offset for i,c in enumerate(cells) if c}
    require((state,head-offset,actual)==(84,-5,target),'Dense replay disagrees on exact frame')
    receipt=dict(status='PASS_EXACT_BLANK_STARTUP_TWO_ENGINES',table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),working_states=len(t)//2,
                 literal_steps=steps,start_state=0,start_head=0,start_tape='all zero',endpoint_state=84,endpoint_head=-5,one_cells=len(target),complete_support=sorted(target),
                 relative_gap=181,physical_primary_values=[0,0,0,3,0,0,3,0,0],spare_values=[1]*167,head_range=[minimum,maximum],
                 row_visits=[dict(row=list(k),visits=n) for k,n in sorted(visits.items())],dense_cross_check=True,
                 scope='Exact finite initialization proof for this literal table; full support equals the independently constructed frame, all other tape cells zero.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in('complete_support','spare_values','row_visits')},indent=2))
if __name__=='__main__':main()
