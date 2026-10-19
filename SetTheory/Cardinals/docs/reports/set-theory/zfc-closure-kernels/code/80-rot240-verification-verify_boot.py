#!/usr/bin/env python3
"""Independent complete-tape initialization and local-clock comparison."""
from pathlib import Path
import argparse, json, hashlib, sys
from collections import Counter
from verify_local import parse, P, sha
if not __debug__ or sys.flags.optimize:raise RuntimeError('Enabled assertions required')

def target_frame():
    ones={-6,176};pos=177
    for n in [0,0,0,3,0,0,3,0,0]+[1]*167:
        pos+=1
        for j in range(n+1):ones.add(pos+j)
        pos+=n+1
    assert len(ones)==351
    return ones

def prefix(table,expected,limit):
    q,h,ones=95,0,set();visits=Counter()
    for steps in range(limit+1):
        if q==96 and h==-5 and ones==expected:return steps,visits
        assert q!=254,('premature halt',steps)
        assert steps<limit,'expected frame not reached'
        b=int(h in ones);visits[q,b]+=1;w,d,q=table[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=P/'evidence/boot_root.json');a=ap.parse_args()
    expected=target_frame();old=parse(P/'reference/rotated241_old.tm');new=parse(P/'machines/zfc240_old.tm')
    oldn,visits=prefix(old,expected,500000);newn,newvisits=prefix(new,expected,500000)
    counts={f'{q}/{b}':visits[q,b]for q,b in[(72,0),(72,1),(90,0),(90,1)]}
    assert counts=={'72/0':74,'72/1':37,'90/0':18,'90/1':24}
    extra=8*visits[72,0]+2*(visits[72,1]+visits[90,0]+visits[90,1])
    assert oldn==408941 and newn==409691 and extra==750 and newn==oldn+extra
    # Different storage and canonical state labels provide a separate execution.
    can=parse(P/'machines/zfc240.tm');cells=bytearray(1);origin=0;head=0;q=0
    for _ in range(newn):
        if head<origin:cells=bytearray(origin-head)+cells;origin=head
        if head>=origin+len(cells):cells.extend(bytearray(head-origin-len(cells)+1))
        w,d,q=can[q,cells[head-origin]];cells[head-origin]=w;head+=d
    all_ones={origin+i for i,b in enumerate(cells)if b}
    assert(q,head,all_ones)==(84,-5,expected)
    out={'status':'ROOT_EXACT_BLANK_AND_CLOCK_PASS','canonical_sha256':sha(P/'machines/zfc240.tm'),
         'old_steps':oldn,'new_steps':newn,'clock_extra':extra,'old_exceptional_visits':counts,
         'endpoint':{'state_old':96,'state_canonical':84,'head':-5,'marker':-6,'header':176,
                     'logical_registers':[3,0,0,0,3,0,0,0,0],
                     'physical_registers':[0,0,0,3,0,0,3,0,0],'spare_values':[1]*167,
                     'all_one_positions':sorted(expected),'all_other_cells_zero':True},
         'independent_representations':['sparse integer set with inherited labels','dynamic dense bytes with canonical labels']}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='endpoint'},indent=2))
if __name__=='__main__':main()
