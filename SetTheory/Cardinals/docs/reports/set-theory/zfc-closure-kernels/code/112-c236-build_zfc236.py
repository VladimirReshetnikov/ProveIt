#!/usr/bin/env python3
"""Build and independently check the rotated-source 236-state candidate.

The local fold is supported by an all-tape positive block proof: the old
states182 and223 have left-neighbor bits1 and0 respectively; each old step
from one of them is simulated in exactly three tape-preserving steps.
This script additionally compares every startup synchronization checkpoint.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
INPUT_HASH='a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a'
ROTATED_HASH='da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724'
OUTPUT_HASH='ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3' 

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def table(p):
    out={};start=None
    for line in p.read_text().splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=int(q),int(b)
        assert key not in out
        out[key]=(int(w),1 if d=='R' else -1,int(z))
    states={q for q,b in out}
    assert start in states and len(out)==2*len(states)
    assert set(out)=={(q,b) for q in states for b in(0,1)}
    return out,start

def encode(t,start):
    return f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
                                      for (q,b),(w,d,z) in sorted(t.items()))

def phi(q):return 182 if q==223 else q

def step(t,q,h,s):
    w,d,z=t[q,int(h in s)]
    if w:s.add(h)
    else:s.discard(h)
    return z,h+d

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input237',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    args=ap.parse_args();dest=args.output_dir;dest.mkdir(exist_ok=True,parents=True)
    assert digest(args.input237)==INPUT_HASH,'Pinned original237 input'
    original,start=table(args.input237)
    assert start==95 and len(original)==474
    old=dict(original)
    old[177,0]=(0,1,185);old[177,1]=(1,1,212)
    old[185,0]=(0,1,165);old[185,1]=(1,1,192)
    rotated=dest/'zfc_rotated237_old.tm';rotated.write_text(encode(old,start))
    assert digest(rotated)==ROTATED_HASH,'Exact four-row source rotation' 
    assert old[182,0]==(0,1,187) and old[182,1]==(1,1,212)
    assert old[223,0]==(0,1,23) and old[223,1]==(1,1,70)
    assert [(q,b,w,d) for(q,b),(w,d,z) in old.items() if z==182]==[(76,1,1,1)]
    assert [(q,b,w,d) for(q,b),(w,d,z) in old.items() if z==223]==[(237,0,0,1)]
    new={(q,b):(w,d,phi(z)) for(q,b),(w,d,z) in old.items() if q!=223}
    new[182,0]=(0,-1,198);new[182,1]=(1,-1,210)
    inherited=dest/'zfc236_old.tm';inherited.write_text(encode(new,start))
    assert digest(inherited)==OUTPUT_HASH,'Exact three-row fold'
    states={q for q,b in new};assert len(states)==236
    order=[start]+sorted(states-{start})
    mapping={q:i for i,q in enumerate(order)}|{254:236}
    canonical={(mapping[q],b):(w,d,mapping[z]) for(q,b),(w,d,z) in new.items()}
    canon=dest/'zfc236.tm';canon.write_text(encode(canonical,0))
    (dest/'renumbering236.json').write_text(json.dumps({'old_to_new':mapping,'start_old':95,
        'start_new':0,'halt_old':254,'halt_new':236,'dispatcher_old':96,'dispatcher_new':mapping[96]},indent=2)+'\n')

    # Exact startup synchronized through the proved local three-step blocks.
    qo=qn=qb=95;ho=hn=hb=0;so=set();sn=set();sb=set();newticks=0;costs=Counter();rotation_visits=Counter()
    for tick in range(409835):
        assert(qn,hn,sn)==(phi(qo),ho,so),(tick,'before')
        assert(qo,ho,so)==(qb,hb,sb),(tick,'rotation_before')
        if (qb,int(hb in sb)) in ((177,0),(177,1),(185,0),(185,1)):
            rotation_visits[qb,int(hb in sb)]+=1
        qb,hb=step(original,qb,hb,sb)
        edge=qo,int(ho in so);n=3 if qo in(182,223) else 1
        if qo in(182,223):costs[edge]+=1
        qo,ho=step(old,qo,ho,so)
        for _ in range(n):qn,hn=step(new,qn,hn,sn)
        newticks+=n
        assert(qn,hn,sn)==(phi(qo),ho,so),(tick,'after')
        assert(qo,ho,so)==(qb,hb,sb),(tick,'rotation_after')
    assert qo==qn==96 and ho==hn==-5 and len(so)==len(sn)==351
    assert newticks==409835+2*sum(costs.values())

    # A dense, canonically relabeled run independently checks the exact tape.
    offset=8192;tape=bytearray(32768);q=0;h=offset
    for _ in range(newticks):
        assert 0<=h<len(tape)
        w,d,z=canonical[q,tape[h]];tape[h]=w;h+=d;q=z
    dense={i-offset for i,b in enumerate(tape) if b}
    assert(q,h-offset,dense)==(mapping[96],-5,sn)
    result={'status':'CONSTRUCTION_AND_EXACT_STARTUP_PASS',
        'input237_sha256':digest(args.input237),'basis_sha256':digest(rotated),'inherited_sha256':digest(inherited),'canonical_sha256':digest(canon),
        'states':236,'rows':472,'start_inherited':95,'start_canonical':0,
        'dispatcher_inherited':96,'dispatcher_canonical':mapping[96],
        'halt_inherited':254,'halt_canonical':236,'deleted':223,'retained':182,
        'old_startup_steps':409835,'new_startup_steps':newticks,'matched_checkpoints':409836,
        'rotation_startup_visits':{f'{q}/{b}':v for(q,b),v in sorted(rotation_visits.items())},
        'exceptional_startup_visits':{f'{q}/{b}':v for(q,b),v in sorted(costs.items())},
        'startup_head':hn,'startup_support':sorted(sn),'canonical_dense_replay':True,
        'rotation_table_edits':[{'row':[q,b],'old':original[q,b],'new':old[q,b]} for q,b in sorted(old) if old[q,b]!=original[q,b]],
        'table_edits':[{ 'row':[q,b],'old':old[q,b],'new':new[q,b]} for q,b in sorted(new) if old[q,b]!=new[q,b]],
        'proof_scope':'Local all-tape block proof and source/runtime calibration are separate certificates.'}
    (dest/'construction236.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='startup_support'},indent=2))

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    main()
