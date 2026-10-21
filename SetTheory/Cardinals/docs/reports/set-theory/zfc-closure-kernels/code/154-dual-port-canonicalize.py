#!/usr/bin/env python3
"""Independent canonical relabelling and complete finite blank initialization.

Adapted from the predecessor canonicalize220.py. No symbolic-runtime imports.
Both sparse and dense simulations must yield the same complete tape.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
from construct import CONFIG,require,dump,sha

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--variant',choices=CONFIG,required=True)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();cfg=CONFIG[a.variant];raw=a.table.read_bytes()
    require(sha(raw)==cfg['table_sha256'],'Native table hash')
    require(sha(a.source.read_bytes())==cfg['source_sha256'],'Source hash')
    T={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            require((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed row')
            T[q,b]=w,1 if d=='R'else-1,z
    Q={q for q,b in T}
    require(starts==[0]and len(Q)==219 and set(T)=={(q,b)for q in Q for b in(0,1)},'State census')
    require({z for w,d,z in T.values()}-Q=={254},'Halting target')
    order=[0];mp={0:0}
    for q in order:
        for b in(0,1):
            z=T[q,b][2]
            if z in Q and z not in mp:mp[z]=len(order);order.append(z)
    require(set(order)==Q,'Unreachable state');mp[254]=219
    U={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    encoded=('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items()))).encode('ascii')
    ticks=312617;q=h=0;ones=set();vis=Counter()
    for _ in range(ticks):
        bit=int(h in ones);vis[q,bit]+=1;w,d,q=T[q,bit]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    origin=ticks+1;tape=bytearray(2*origin+1);cq=0;ch=origin;cvis=Counter()
    for _ in range(ticks):
        bit=tape[ch];cvis[cq,bit]+=1;w,d,cq=U[cq,bit];tape[ch]=w;ch+=d
    cones={i-origin for i,b in enumerate(tape)if b}
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9;phy=[6,2,0,4,3,7,8,5,1]
    for i,j in enumerate(phy):physical[j]=logical[i]
    expected={-6,139};cursor=140
    for n in physical+[1]*130:
        cursor+=1;expected.update(range(cursor,cursor+n+1));cursor+=n+1
    require((q,h,ones)==(84,-5,expected),'Native complete blank frame differs')
    require((cq,ch-origin,cones)==(mp[84],-5,expected),'Canonical complete blank frame differs')
    require(cvis==Counter({(mp[q],b):n for(q,b),n in vis.items()}),'Relabelled visits differ')
    require(len(expected)==277,'Support census')
    a.output.mkdir(parents=True,exist_ok=True);(a.output/'candidate.tm').write_bytes(encoded)
    result={'status':'CANONICAL_TABLE_AND_COMPLETE_BLANK_STARTUP_PASS','variant':a.variant,
      'working_states':219,'rows':438,'start':0,'halt':219,'dispatcher':mp[84],
      'native_to_canonical':mp,'native_sha256':sha(raw),'canonical_sha256':sha(encoded),
      'source_sha256':cfg['source_sha256'],
      'startup':{'steps':ticks,'native_state':q,'canonical_state':cq,'head':h,
        'one_cells':sorted(ones),'all_other_cells':0,'logical_registers':logical,
        'physical_registers':physical,'physical_map':phy,'extra_gap':80,'spares':[1]*130,
        'sparse_and_dense_simulations_agree':True},
      'scope':'Finite complete initialization and literal bijection; unbounded simulation is a separate obligation.'}
    dump(a.output/'canonicalization.json',result)
    print(a.variant,result['status'],result['canonical_sha256'],flush=True)
if __name__=='__main__':main()
