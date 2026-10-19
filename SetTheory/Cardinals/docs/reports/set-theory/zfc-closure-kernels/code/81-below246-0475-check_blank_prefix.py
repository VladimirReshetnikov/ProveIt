#!/usr/bin/env python3
"""Independent fixed-prefix replay; no initial-state or bootstrap search.

The exact acceptance condition is state96, head-5, and the complete known
safe-root tape, including all167 spare blocks and zero exterior. Bounded
negative outcomes assert only failure to reach that exact frame by the
stated transition bound. A reference trajectory difference is diagnostic,
not by itself a semantic counterexample.
"""
from pathlib import Path
import argparse,hashlib,json,time

BOUND=410735;OFFSET=2048;SIZE=8192;START=95;HALT=254
PRIMARY=[0,0,0,3,0,0,3,0,0]

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read_table(path):
    T={};start=None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        fields=line.split();assert len(fields)==5
        q,b,w,d,t=fields;q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in T
        T[q,b]=(w,-1 if d=='L' else 1,t)
    states={q for q,b in T};assert start==START
    assert len(T)==2*len(states)
    assert all((q,b) in T for q in states for b in (0,1))
    assert {t for w,d,t in T.values()}-states=={HALT}
    return T

def target_tape():
    a=bytearray(SIZE);a[OFFSET-6]=1;a[OFFSET+176]=1;x=OFFSET+177
    for v in PRIMARY+[1]*167:
        assert a[x]==0
        for k in range(v+1):a[x+1+k]=1
        x+=v+2
    assert sum(a)==351
    return a

def step(T,tape,q,h):
    assert 0<=h<SIZE,'head left the explicit window'
    w,d,n=T[q,tape[h]];tape[h]=w;return n,h+d

def replay_reference(T,want):
    a=bytearray(SIZE);q=START;h=OFFSET;lo=hi=h;first=None
    for tick in range(1,BOUND+1):
        assert q!=HALT
        q,h=step(T,a,q,h);lo=min(lo,h);hi=max(hi,h)
        if first is None and q==96 and h==OFFSET-5 and a==want:first=tick
    assert (q,h)==(96,OFFSET-5) and a==want
    return dict(status='PASS',steps=BOUND,first_exact_frame=first,
                head_window=[lo-OFFSET,hi-OFFSET],complete_tape_equality=True)

def replay(T,R,want):
    a=bytearray(SIZE);r=bytearray(SIZE);q=rq=START;h=rh=OFFSET
    lo=hi=h;first_config=None;first_tape=None;different=0;hit=None;stop=None
    for tick in range(1,BOUND+1):
        if q==HALT:stop='halt';tick-=1;break
        if not 0<=h<SIZE:stop='explicit tape boundary';tick-=1;break
        assert rq!=HALT and 0<=rh<SIZE
        b=a[h];rb=r[rh];tr=T[q,b];rr=R[rq,rb]
        before=dict(state=q,head=h-OFFSET,read=b)
        ref_before=dict(state=rq,head=rh-OFFSET,read=rb)
        w,d,n=tr;rw,rd,rn=rr
        different+=int(w!=r[h])-int(a[h]!=r[h]);a[h]=w
        different+=int(a[rh]!=rw)-int(a[rh]!=r[rh]);r[rh]=rw
        q,h=n,h+d;rq,rh=rn,rh+rd;lo=min(lo,h);hi=max(hi,h)
        if first_config is None and (q!=rq or h!=rh or different):
            first_config=dict(transition=tick,candidate_entry=before,
                reference_entry=ref_before,
                candidate_row=[tr[0],'L' if tr[1]==-1 else 'R',tr[2]],
                reference_row=[rr[0],'L' if rr[1]==-1 else 'R',rr[2]],
                candidate_exit=dict(state=q,head=h-OFFSET),
                reference_exit=dict(state=rq,head=rh-OFFSET),
                different_tape_cells=different)
        if first_tape is None and different:
            positions=[i-OFFSET for i,(x,y) in enumerate(zip(a,r)) if x!=y]
            first_tape=dict(transition=tick,different_cell_count=different,
                            first_different_cells=positions[:20])
        if q==96 and h==OFFSET-5 and a==want:
            hit=tick;stop='first exact safe-root frame';break
    else:tick=BOUND;stop='fixed transition bound'
    diff=[i-OFFSET for i,(x,y) in enumerate(zip(a,want)) if x!=y]
    out=dict(status='PASS' if hit is not None else 'NOT_REACHED_WITHIN_BOUND',
        transition_bound=BOUND,transitions_executed=tick,first_exact_frame=hit,
        stop_reason=stop,final_state=q,final_head=h-OFFSET,
        final_one_count=sum(a),head_window=[lo-OFFSET,hi-OFFSET],
        complete_tape_equals_target=a==want,
        target_tape_difference_count=len(diff),first_target_difference_cells=diff[:30],
        first_configuration_difference_from_reference=first_config,
        first_tape_difference_from_reference=first_tape)
    if hit is not None:
        assert (q,h)==(96,OFFSET-5) and a==want
        out['safe_root']=dict(state=96,head=-5,marker=-6,header=176,
            header_distance=181,pc='',physical_primary=PRIMARY,
            logical_primary=[3,0,0,0,3,0,0,0,0],spare_count=167,
            every_spare_value=1,ones=351,zero_everywhere_else=True)
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference',type=Path,required=True)
    ap.add_argument('--table',type=Path,action='append',required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();began=time.monotonic();R=read_table(args.reference);want=target_tape()
    reference=replay_reference(R,want)
    outcomes=[]
    for path in args.table:
        T=read_table(path);out=replay(T,R,want)
        out.update(table=str(path),table_sha256=digest(path),working_states=len(T)//2)
        outcomes.append(out);print(path,out['status'],out['transitions_executed'],
            out['final_state'],out['final_head'],out['target_tape_difference_count'],flush=True)
    result=dict(status='PASS' if all(o['status']=='PASS' for o in outcomes) else 'FAIL',
        check_kind='fixed-prefix exact safe-root replay',checker_sha256=digest(__file__),
        start_state=START,start_head=0,start_tape='all zero',halt_state=HALT,
        transition_bound=BOUND,explicit_tape_coordinates=[-OFFSET,SIZE-OFFSET-1],
        all_cells_outside_explicit_window_remain_zero=True,
        reference_table_sha256=digest(args.reference),reference_check=reference,
        acceptance='state96 and head-5 and exact complete safe-root tape; no spare relaxation',
        no_search=True,outcomes=outcomes,seconds=time.monotonic()-began)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if result['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
