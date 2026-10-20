#!/usr/bin/env python3
"""Independent literal table bijection and exact complete blank startup.

This script does not import the constructor or either symbolic runtime module.
Native simulation uses a sparse set; canonical simulation uses a dense tape.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, sys

def need(x,m):
    if not x: raise ValueError(m)
def sha(raw): return hashlib.sha256(raw).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); out=args.output; out.mkdir(parents=True,exist_ok=True)
    raw=args.table.read_bytes()
    need(sha(raw)=='4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4','Exact native K220 table required')
    need(sha(args.source.read_bytes())=='837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7','Exact K220 source required')
    T={}; starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            need((q,b)not in T and b in(0,1) and w in(0,1) and d in('L','R'),'Malformed row')
            T[q,b]=(w,1 if d=='R' else -1,z)
    Q={q for q,b in T}
    need(starts==[0] and len(Q)==220 and set(T)=={(q,b)for q in Q for b in(0,1)},'State census or completeness')
    need({z for w,d,z in T.values()}-Q=={254},'Terminal census')
    order=[0]; mp={0:0}
    for q in order:
        for b in(0,1):
            z=T[q,b][2]
            if z in Q and z not in mp:mp[z]=len(order);order.append(z)
    need(set(order)==Q,'Graph-unreachable working state');mp[254]=220
    U={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    encoded=('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items()))).encode('ascii')
    need(sha(encoded)=='f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f','Canonical byte identity differs')
    (out/'k220.tm').write_bytes(encoded)
    ticks=409835; q=0;h=0;ones=set();vis=Counter()
    for _ in range(ticks):
        bit=int(h in ones);vis[q,bit]+=1;w,d,q=T[q,bit]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    origin=ticks+1; tape=bytearray(2*origin+1); cq=0;ch=origin;cvis=Counter()
    for _ in range(ticks):
        bit=tape[ch];cvis[cq,bit]+=1;w,d,cq=U[cq,bit];tape[ch]=w;ch+=d
    cones={i-origin for i,b in enumerate(tape)if b}
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9;phy=[6,2,0,4,3,7,8,5,1]
    for i,j in enumerate(phy):physical[j]=logical[i]
    expected={-6,176};cursor=177
    for n in physical+[1]*167:
        cursor+=1;expected.update(range(cursor,cursor+n+1));cursor+=n+1
    need((q,h,ones)==(84,-5,expected),'Sparse native complete blank frame differs')
    need((cq,ch-origin,cones)==(mp[84],-5,expected),'Dense canonical complete blank frame differs')
    need(cvis==Counter({(mp[q],b):n for(q,b),n in vis.items()}),'Relabeled transition counts differ')
    need(len(expected)==351,'Unexpected nonblank support')
    result=dict(status='INDEPENDENT_K220_CANONICALIZATION_AND_COMPLETE_BLANK_STARTUP_PASS',
        working_states=220,rows=440,start=0,halt=220,dispatcher=mp[84],
        native_to_canonical=mp,canonical_to_native={v:k for k,v in mp.items()},
        rule='Breadth first from native0, read0 before read1; terminal254 maps to220',
        native_sha256=sha(raw),canonical_sha256=sha(encoded),source_sha256=sha(args.source.read_bytes()),
        startup=dict(steps=ticks,native_state=q,canonical_state=cq,head=h,one_cells=sorted(ones),all_other_cells=0,
            logical_registers=logical,physical_registers=physical,physical_map=phy,extra_gap=117,spares=[1]*167,
            used_native_rows=[list(k)+[n]for k,n in sorted(vis.items())],sparse_and_dense_simulations_agree=True),
        scope='Exact table bijection and complete finite blank initialization; unbounded runtime and consistency calibration are separate obligations.')
    (out/'canonicalization.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k]for k in ('status','working_states','rows','dispatcher','canonical_sha256')},indent=2))
if __name__=='__main__':main()
