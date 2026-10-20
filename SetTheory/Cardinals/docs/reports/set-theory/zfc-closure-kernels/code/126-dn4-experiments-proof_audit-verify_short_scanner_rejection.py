#!/usr/bin/env python3
"""Literal counterexamples to deleting scanner state 50.

Standard library only. Inputs are the pinned normalized original K225 and
accepted DN4 tables. The original valid-runtime-frame failure is exact; the
DN4 blank trace separately identifies the false reset at a seven-zero gap.
"""
from pathlib import Path
import argparse,hashlib,json

BASE_SHA='0847184fa05327daefa45c7012ce2c75fe58bf03d1dc930fe152e9fac55b4fbc'
DN4_SHA='3b958e7bc60964dbd95c0d244c3183cc91920a89ed12139cde8e973ae55754f4'

def require(x,message):
    if not x:raise ValueError(message)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def parse(path):
    table={}; starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R'),'Malformed transition')
        table[q,b]=(w,1 if d=='R' else -1,z)
    states={q for q,b in table}
    require(starts==[0] and 0 in states and 254 not in states,'Wrong start/halt')
    require(set(table)=={(q,b) for q in states for b in (0,1)},'Partial table')
    require({z for w,d,z in table.values()}-states=={254},'Wrong terminal state')
    return table

def shorten(table):
    result=dict(table)
    require(result[34,0]==(0,-1,50) and result[50,0]==(0,-1,75),'Wrong scanner layout')
    result[34,0]=(0,-1,75)
    del result[50,0],result[50,1]
    require(not any(z==50 for w,d,z in result.values()),'State50 is still referenced')
    return result

def encoded(table):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
             for (q,b),(w,d,z) in sorted(table.items()))).encode()

def frame(pc):
    # Nine zero registers and one zero spare, with the retained width64 header.
    return {-1,64}|{i for i,b in enumerate(pc) if b=='1'}|set(range(66,85,2))

def step(table,q,h,tape):
    b=int(h in tape);w,d,z=table[q,b]
    if w:tape.add(h)
    else:tape.discard(h)
    return z,h+d

def output(q,h,tape,n,**extra):
    return dict(steps=n,state=q,head=h,one_cells=sorted(tape),all_other_cells=0,**extra)

def exact_frame_run(table,pc,target_pc,n):
    tape=frame(pc);q,h=84,0
    for k in range(n):q,h=step(table,q,h,tape)
    require((q,h)==(84,0) and tape==frame(target_pc),'Concrete final frame did not reproduce')
    return output(q,h,tape,n,path=target_pc)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--dn4',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    require(digest(a.baseline)==BASE_SHA,'Wrong original225 table')
    require(digest(a.dn4)==DN4_SHA,'Wrong DN4 table')
    base=parse(a.baseline);base_short=shorten(base)
    dn4=parse(a.dn4);dn4_short=shorten(dn4)
    pc='11101001001000000'
    good_pc='111010010010000100';bad_pc='11101001001001000'
    good=exact_frame_run(base,pc,good_pc,586)
    bad=exact_frame_run(base_short,pc,bad_pc,662)
    require(good['one_cells']!=bad['one_cells'],'No runtime counterexample')
    concrete=dict(source_index=40,site=[pc,'CD',1],guard='zero',
        input=dict(state=84,head=0,path=pc,header_width=64,logical_registers=[0]*9,
                   spares=[0],one_cells=sorted(frame(pc)),all_other_cells=0),
        reference=good,rejected=bad)
    tape=set();q=h=0;visits={0:0,1:0};obstruction=None
    for k in range(409835):
        b=int(h in tape)
        if q==50:visits[b]+=1
        if (q,h)==(34,0) and k==47000:
            obstruction=output(q,h,tape,k)
        q,h=step(dn4,q,h,tape)
    require((q,h,len(tape))==(84,-5,351),'Wrong reference blank initialization')
    require(visits=={0:1410,1:1} and obstruction is not None,'Wrong scanner startup trace')
    reference_boot=output(q,h,tape,409835,q50_read_visits=visits)
    target=set(obstruction['one_cells'])
    require(all(i not in target for i in range(7)) and -1 in target and 7 in target,
            'Missing exactly-seven-zero gap')
    tape=set();q=h=0
    for k in range(46198):q,h=step(dn4_short,q,h,tape)
    require((q,h)==(34,0) and tape==target,'Candidate does not reach the common obstruction')
    candidate_common=output(q,h,tape,46198)
    old_local=set(target);oq,oh=34,0
    for k in range(2):oq,oh=step(dn4,oq,oh,old_local)
    for k in range(2):q,h=step(dn4_short,q,h,tape)
    require((oq,oh)==(2,-2) and (q,h)==(84,0) and old_local==tape==target,
            'Local false reset did not reproduce')
    false_reset=output(q,h,tape,46200)
    for k in range(46200,1000000):q,h=step(dn4_short,q,h,tape)
    require((q,h,len(tape))==(10,128,676),'Wrong finite candidate startup diagnostic')
    diagnostic=output(q,h,tape,1000000)
    result=dict(status='CONCRETE_REJECTION_REPLAY_PASS',checker_sha256=digest(Path(__file__)),
        original_table_sha256=BASE_SHA,dn4_table_sha256=DN4_SHA,
        shortened_original_sha256=hashlib.sha256(encoded(base_short)).hexdigest(),
        shortened_dn4_sha256=hashlib.sha256(encoded(dn4_short)).hexdigest(),
        patch=dict(row=[34,0],before=[0,-1,50],after=[0,-1,75],remove_state=50),
        original_source_counterexample=concrete,
        dn4_startup=dict(reference=reference_boot,reference_common_predecessor=obstruction,
            candidate_common_predecessor=candidate_common,
            reference_two_step_output=output(oq,oh,old_local,47002),
            candidate_false_reset=false_reset,candidate_million_step_diagnostic=diagnostic),
        conclusion='The 224-state scanner deletion is rejected: a valid all-zero runtime frame has the wrong successor, and the candidate blank run makes an early false reset at a fixed seven-zero initialization gap.',
        limitation='The million-step diagnostic is finite and makes no assertion about whether the malformed startup might later reach some reference configuration.')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('original_source_counterexample','dn4_startup')},indent=2))
    print('Concrete primitive durations: 586 and 662; common startup predecessor: 47000 and 46198.')

if __name__=='__main__':main()
