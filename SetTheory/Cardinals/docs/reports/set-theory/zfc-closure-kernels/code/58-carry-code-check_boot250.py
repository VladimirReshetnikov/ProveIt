#!/usr/bin/env python3
"""Independently replay and compare the complete 585431-step blank bootstrap."""
from pathlib import Path
import argparse, hashlib, json, time
from collections import Counter
from check_candidate250 import read_table


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--table',type=Path,default=Path(__file__).resolve().parents[1]/'machine/zfc_prefix250_old.tm')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'evidence/final250-boot-audit.json')
    args=ap.parse_args();T=read_table(args.table)
    assert len(T)==500 and len({q for q,b in T})==250
    one=set();head=0;q=97;used=Counter();began=time.monotonic()
    for t in range(585431):
        assert q!=254,(t,'unexpected halt')
        key=q,int(head in one);used[key]+=1;w,d,q=T[key]
        if w:one.add(head)
        else:one.discard(head)
        head+=d
    assert q==96 and head==-3 and head-1 in one
    assert all(i>=head-1 for i in one)
    header=min(i for i in one if i>=head)
    assert header==225
    values=[];pos=header+1
    while pos<=max(one):
        assert pos not in one and pos+1 in one
        start=pos+1;pos=start
        while pos in one:pos+=1
        values.append(pos-start-1)
    assert values[:9]==[0,2,0,4,0,0,1,0,0]
    assert len(values)==219 and values[9:]==[1]*210
    expected={head-1,header};x=header+1
    for v in values:
        expected.update(range(x+1,x+v+2));x+=v+2
    assert expected==one and len(one)==438
    assert used[97,0]==1
    out=dict(status='PASS',blank_steps=585431,entry_state=97,state=q,head=head,
             marker=head-1,header=header,header_distance=header-head,pc='',
             one_count=len(one),primary_physical=values[:9],
             primary_logical=[values[i] for i in [6,2,0,4,3,7,8,5,1]],
             spare_count=len(values)-9,spare_values=values[9:],
             all_one_positions=sorted(one),all_other_cells_zero=True,
             initializer_transition_uses=used[97,0],rollback_transition_uses=used[97,1],
             finite_replay_only=True,seconds=time.monotonic()-began,
             table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest())
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('all_one_positions','spare_values')},indent=2))

if __name__=='__main__':main()
