#!/usr/bin/env python3
"""Reproduce an exact whole-tape register error in a rejected state merge.

No assertion about the candidate's eventual blank-tape halting is made.
"""
from pathlib import Path
import json
from verify import table, require

ROOT=Path(__file__).resolve().parents[1]
PHY=(6,2,0,4,3,7,8,5,1)

def frame(path,values,spares):
    bits={-1,56}|{i for i,b in enumerate(path) if b=='1'}
    cursor=57; physical=[0]*9
    for i,j in enumerate(PHY):physical[j]=values[i]
    for value in physical+spares:
        cursor+=1
        bits.update(range(cursor,cursor+value+1))
        cursor+=value+1
    return bits

def run(rows,initial,final,bound):
    bits=initial.copy();q=84;head=0
    for k in range(1,bound+1):
        require(q!=254,'Unexpected early halt')
        w,d,q=rows[q,int(head in bits)]
        if w:bits.add(head)
        else:bits.discard(head)
        head+=1 if d=='R' else -1
        if (q,head,bits)==(84,0,final):return k
    raise ValueError('Specified full-tape endpoint not reached')

def main():
    old,start,halt=table(ROOT/'data/pa196.native.tm')
    require((start,halt)==(74,254),'Native control convention')
    new={(q,b):(w,d,124 if z==109 else z)
         for (q,b),(w,d,z) in old.items() if q!=109}
    pc='0100110110';successor='0100110111'
    initial=frame(pc,[0]*9,[0]);expected=[0]*9;wrong=[0]*9
    expected[6]=1;wrong[8]=1
    a=run(old,initial,frame(successor,expected,[0,1]),596)
    b=run(new,initial,frame(successor,wrong,[0,1]),574)
    require((a,b)==(596,574),'Exact recorded durations changed')
    print(json.dumps(dict(status='CANDIDATE_REJECTED',drop_native=109,keep_native=124,
        drop_dense=96,keep_dense=103,site_index=16,path=pc,successor=successor,
        header_gap=56,initial_registers=[0]*9,initial_spares=[0],parent_steps=a,
        candidate_steps=b,parent_registers=expected,candidate_registers=wrong,
        final_spares=[0,1],scope='Whole-tape primitive mismatch; no blank-halting conclusion.'),indent=2))

if __name__=='__main__':main()
