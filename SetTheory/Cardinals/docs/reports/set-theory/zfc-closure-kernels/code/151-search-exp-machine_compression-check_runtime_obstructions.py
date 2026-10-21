#!/usr/bin/env python3
"""Reproduce finite obstructions and exact blank endpoints; Python3 stdlib only.
This does not certify any217-state machine as equivalent to Con(ZFC).
"""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PHY=(6,2,0,4,3,7,8,5,1)

def table(name):
    t={}
    for line in (ROOT/name).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b)not in t and d in('L','R')
        t[q,b]=(w,1 if d=='R' else -1,z)
    assert len({q for q,b in t})==217 and len(t)==434
    return t

def run(t,q,h,ones,n):
    ones=set(ones)
    for _ in range(n):
        w,d,q=t[q,int(h in ones)]
        ones.discard(h)
        if w:ones.add(h)
        h+=d
    return q,h,ones

def decode(h,ones):
    assert h-1 in ones and min(ones)==h-1
    header=min(x for x in ones if x>=h+52)
    assert header>=h+64
    p=header+1;last=max(ones);values=[]
    while p<=last:
        assert p not in ones and p+1 in ones
        first=p+1;p=first
        while p in ones:p+=1
        values.append(p-first-1)
    assert p==last+1 and len(values)>=10
    return [values[i]for i in PHY],values[9:],header-h-64

def frame(pc,regs,spares,gap):
    values=[None]*9
    for j,i in enumerate(PHY):values[i]=regs[j]
    ones={-1,64+gap}|{j for j,b in enumerate(pc)if b=='1'}
    p=65+gap
    for v in values+spares:
        p+=1;ones.update(range(p,p+v+1));p+=v+1
    return ones

core=table('delete301-runtime-core.tm')
obstruction=json.loads((ROOT/'delete301-blank-obstruction.json').read_text())
q,h,ones=run(core,0,0,set(),85)
assert (q,h,sorted(ones))==(35,7,obstruction['ones'])
assert core[35,0]==(1,1,35) and not any(x>=h for x in ones)
print('CORE: exact85-step prefix enters an infinite rightward blank ray.')

for target in (6,10,16):
    receipt=json.loads((ROOT/f'bootstrap-{target}-receipt.json').read_text())
    t=table(receipt['table']);boot=receipt['blank_endpoint']
    q,h,ones=run(t,0,0,set(),boot['steps'])
    regs,spares,gap=decode(h,ones)
    assert q==84 and h==boot['head']
    assert regs==boot['registers'] and len(spares)==boot['spare_count'] and gap==boot['gap']
    assert not any(h<=x<h+52 for x in ones)
    if target in (6,10):
        actual_initial={x-h for x in ones}
        actual_expected=frame('01',regs,spares,gap)
        aq,ah,atape=run(t,84,0,actual_initial,688)
        assert aq==84 and ah==0 and atape!=actual_expected
        decode(ah,atape)
        extra=receipt['actual_startup_successor_failure']
        assert sorted(actual_initial)==extra['initial_ones']
        assert sorted(actual_expected)==extra['expected_ones']
        assert sorted(atape)==extra['observed_ones']
        print(f'BOOTSTRAP{target}: actual first primitive returns incorrectly after688 further steps.')
    witness=receipt['runtime_test'];initial=set(witness['initial_ones'])
    regs,spares,gap=decode(0,initial)
    assert initial==frame('000',regs,spares,gap)
    if regs[8]>0:
        regs[8]-=1;pc='001';gap+=1
    else:pc='01'
    expected=frame(pc,regs,spares,gap)
    assert expected==set(witness['expected_ones'])
    q,h,ones=run(t,84,0,initial,1232)
    assert q==84 and h==0
    decode(h,ones) # The wrong result is nevertheless a well-formed canonical frame.
    assert ones!=expected
    assert (q,h,sorted(ones))==(witness['observed_state'],witness['observed_head'],witness['observed_ones'])
    print(f'BOOTSTRAP{target}: exact blank endpoint at{boot["steps"]} steps; source CD8 interface fails at1232 steps.')
print('PASS: all stated obstructions reproduced. No Con(ZFC) candidate is certified.')
