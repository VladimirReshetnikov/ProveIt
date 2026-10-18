#!/usr/bin/env python3
"""Prepared valid source-phase counterexample probe, not a blank-run result."""
from pathlib import Path
import argparse
import hashlib
import json
import time

ROOT=Path(__file__).resolve().parent
PHYS=(6,2,0,4,3,7,8,5,1)
TABLE_SHA256='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
PROGRAM_SHA256='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def table(path):
    t={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,a,w,d,r=line.split();t[int(q),int(a)]=(int(w),1 if d=='R' else -1,int(r))
    return t

def paint(pc,logical,spares,gap=40):
    ones={-1,gap}
    ones.update(i for i,b in enumerate(pc) if b=='1')
    values=[logical[PHYS.index(r)] for r in range(9)]+spares
    p=gap+1
    for v in values:ones.update(range(p+1,p+v+2));p+=v+2
    return ones

def frame(ones,h):
    if {p for p in ones if p<h}!={h-1}:return None
    right=[p for p in ones if p>=h]
    if not right:return None
    header=min(right)
    if header-h<40:return None
    vals=[];p=header+1;end=max(ones)
    while p<=end:
        if p in ones:return None
        p+=1;n=0
        while p in ones:n+=1;p+=1
        if n==0:return None
        vals.append(n-1)
    if len(vals)<10:return None
    return {'head':h,'header':header,'gap':header-h,'logical':[vals[r] for r in PHYS],'spares':vals[9:]}

def run(t,label,limit=5000000,gap=40,spare_count=3,next_candidate=0):
    # At successful-MP restoration: T=2, D=1, X=1, hence T=D+X.
    # Code 2 = All(0,truth), derivable.  The original MP can be supplied by
    # T_old=truth and H_old=Imp(truth,All(0,truth))=20, also derivable.
    # L=151 makes the next two source commands NIP(0), NIP(0).
    logical=[next_candidate,2,0,0,1,0,1,0,151]
    ones=paint('1111111111',logical,[1]*spare_count,gap)
    initial=sorted(ones)
    q=96;h=0;frames=[];visits=0;started=time.monotonic()
    for step in range(1,limit+1):
        w,d,r=t[q,int(h in ones)]
        if (q,int(h in ones))==(172,1):visits+=1
        if w:ones.add(h)
        else:ones.discard(h)
        q=r;h+=d
        if q==254:break
        if q==96:
            fr=frame(ones,h)
            if fr is not None:
                frames.append({'step':step,**fr})
    return {'label':label,'status':'HALTED_FROM_PREPARED_PHASE' if q==254 else 'FUEL_CUTOFF','steps':step,'state':q,'head':h,'changed_row_visits':visits,'frames':frames[:8],'total_root_frames':len(frames),'initial_logical':logical,'initial_pc':'1111111111','initial_gap':gap,'initial_spare_count':spare_count,'initial_ones':initial,'final_ones':sorted(ones),'seconds':time.monotonic()-started}

def dense_verify(t,result):
    # Separate dense-tape representation and transition loop, with checked
    # array bounds.  Untouched exterior cells are consequently all zero.
    offset=4096
    a=bytearray(16384)
    for p in result['initial_ones']:a[offset+p]=1
    rows=[None]*512
    for (q,bit),(w,d,r) in t.items():rows[2*q+bit]=(w,d,r)
    q=96;pos=offset
    for i in range(result['steps']):
        assert 0<=pos<len(a) and q!=254
        row=rows[2*q+a[pos]]
        assert row is not None
        a[pos]=row[0];pos+=row[1];q=row[2]
    support=[j-offset for j,b in enumerate(a) if b]
    assert (q,pos-offset,support)==(result['state'],result['head'],result['final_ones'])
    return {'status':'PASS','steps':result['steps'],'same_state_head_and_complete_tape':True,'checked_dense_bounds':True}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--program',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=Path('state204_safe_phase_probe.json'))
    args=ap.parse_args()
    assert hashlib.sha256(args.table.read_bytes()).hexdigest()==TABLE_SHA256
    assert hashlib.sha256(args.program.read_bytes()).hexdigest()==PROGRAM_SHA256
    base=table(args.table);mut={k:v for k,v in base.items() if k[0]!=204}
    assert len(base)==492 and len(mut)==490
    assert base[172,1]==(1,1,204)
    mut[172,1]=(1,1,252)
    assert all(r!=204 for w,d,r in mut.values())
    out=run(mut,'prefix246_delete204_target252')
    assert out['status']=='HALTED_FROM_PREPARED_PHASE' and out['steps']==12808
    assert (out['state'],out['head'],out['changed_row_visits'],out['total_root_frames'])==(254,12,3,0)
    out['independent_dense']=dense_verify(mut,out)
    baseline=run(base,'unmodified_prefix246',3317)
    assert baseline['frames'][-1]['logical']==[0,2,0,0,2,0,0,0,151]
    assert baseline['frames'][0]['step']==3317
    assert baseline['frames'][0]['spares']==[1]*4
    baseline['independent_dense']=dense_verify(base,baseline)
    out['baseline_first_root']=baseline
    large=run(mut,'same_phase_actual_bootstrap_margin_and_spares',gap=181,spare_count=167,next_candidate=3)
    assert (large['status'],large['steps'],large['state'],large['head'],large['changed_row_visits'],large['total_root_frames'])==('HALTED_FROM_PREPARED_PHASE',10232,254,12,3,0)
    large['independent_dense']=dense_verify(mut,large)
    out['stronger_resources_control']=large
    pair=lambda x,y:(x+y)*(x+y+1)//2+y
    assert pair(2,pair(0,0))==3
    assert pair(2,pair(0,4))==150
    assert 4*pair(0,2)==20
    out['source_phase_explanation']={
        'starting_MP_root_logical':[0,0,0,0,2,20,0,0,pair(0,pair(0,151))+1],
        'current_formula_2':'All(0,truth), obtained by generalization',
        'original_cache_20':'Imp(truth,All(0,truth)), obtained from the theorem All(0,truth) by propositional K and MP',
        'phase':'First restoration-loop continue after copying goal2 into TW and scratch1',
        'tail_151':'One plus the packed command sequence NIP(0),NIP(0)',
        'scope':'Prepared source-phase halting obstruction only; no assertion of mutant reachability from blank or blanket semantic inequivalence.'}
    from source_phase_certificate import certificate
    out['source_phase_certificate']=certificate(args.program)
    out['table_sha256']=TABLE_SHA256
    out['program_sha256']=PROGRAM_SHA256
    out['blank_reachability_proved']=False
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('initial_ones','final_ones','baseline_first_root','stronger_resources_control','source_phase_certificate')},indent=2))
    print(json.dumps({'stronger_resources_control':{k:v for k,v in large.items() if k not in ('initial_ones','final_ones')}},indent=2))

if __name__=='__main__':main()
