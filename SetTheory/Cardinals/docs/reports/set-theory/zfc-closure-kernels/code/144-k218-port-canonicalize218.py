#!/usr/bin/env python3
"""Independent dense/sparse replay of the exact complete K218 blank startup."""
from pathlib import Path
from collections import Counter
import argparse,json
from common import *

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    raw=a.table.read_bytes();require(sha(raw)==TABLE_SHA and sha_file(a.sites)==SOURCE_SHA,'Pinned exact K218 inputs')
    T=parse_table(raw);Q={q for q,bit in T};require(len(Q)==218 and len(T)==436,'State census')
    order=[0];mp={0:0}
    for q in order:
        for bit in(0,1):
            z=T[q,bit][2]
            if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
    require(set(mp)==Q,'All working states must be graph reachable');mp[254]=218
    U={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()};encoded=table_bytes(U)
    require(sha(encoded)==CANONICAL_SHA,'Canonical bytes differ');parse_table(encoded,halt=218)
    ticks=312909;q=0;h=0;ones=set();visits=Counter()
    for _ in range(ticks):
        bit=int(h in ones);visits[q,bit]+=1;w,d,q=T[q,bit]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    origin=ticks+1;array=bytearray(2*origin+1);cq=0;ch=origin;cvisits=Counter()
    for _ in range(ticks):
        bit=array[ch];cvisits[cq,bit]+=1;w,d,cq=U[cq,bit];array[ch]=w;ch+=d
    canonical_ones={i-origin for i,bit in enumerate(array)if bit}
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    expected={-6,139};pos=140
    for value in physical+[1]*130:
        pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
    require((q,h,ones)==(84,-5,expected),'Native whole-tape startup differs')
    require((cq,ch-origin,canonical_ones)==(23,-5,expected),'Canonical whole-tape startup differs')
    require(cvisits==Counter({(mp[q],bit):n for(q,bit),n in visits.items()}),'Canonical transition counts differ')
    require(len(expected)==277 and mp[84]==23,'Blank-frame census')
    a.output.mkdir(parents=True,exist_ok=True);(a.output/'k218.tm').write_bytes(encoded)
    receipt=dict(status='EXACT_K218_CANONICALIZATION_AND_BLANK_STARTUP_PASS',working_states=218,transition_rows=436,start=0,halt=218,dispatcher=23,
        table_sha256=TABLE_SHA,canonical_sha256=CANONICAL_SHA,source_sha256=SOURCE_SHA,native_to_canonical=mp,
        canonical_to_native={v:k for k,v in mp.items()},rule='Breadth first from native0, read0 before read1; terminal254 maps to218',
        startup=dict(steps=ticks,native_state=84,canonical_state=23,head=-5,header=139,extra_gap=80,logical_registers=logical,
            physical_registers=physical,physical_map=PHY,spares=[1]*130,one_cells=sorted(ones),all_other_cells=0,
            used_native_rows=[list(k)+[n]for k,n in sorted(visits.items())],sparse_and_dense_simulations_agree=True),
        scope='Exact label bijection and complete finite blank initialization. Unbounded runtime and calculus calibration are separate obligations.')
    dump(a.output/'canonicalization.json',receipt);print(json.dumps({k:receipt[k]for k in('status','working_states','transition_rows','dispatcher','canonical_sha256')},indent=2))
if __name__=='__main__':main()
