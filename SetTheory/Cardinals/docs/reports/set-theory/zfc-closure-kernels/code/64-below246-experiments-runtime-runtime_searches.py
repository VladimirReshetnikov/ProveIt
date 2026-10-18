"""Reproduce the bounded runtime and coordinated-entry screening experiments.

These searches reject candidates only within explicitly stated finite/local
protocols. They prove no lower bound and no general impossibility theorem.
Set ZFC246_BASE to the pristine context246 archive directory.
"""
from pathlib import Path
from collections import Counter
import argparse,json,time
from search_tail import T,BASE,BASE_SHA256,sim
import check_literal_instructions as chk

HERE=Path(__file__).resolve().parent
RAW_EXPECTED=chk.expected
MACRO_CASES={
    'delete255':[('z',[0,0],0),('i',[0,0],0),('z',[3,0,2],1),('i',[3,2,0],1),('i',[2,0,3,1],2)],
    'delete75':[('p',[1,0],0),('z',[0,0],0),('i',[0,0],0),('p',[3,2,2],1),('z',[3,0,2],1),('i',[3,2,0],1),('i',[2,0,3,1],2)],
    'ones_tail':[('z',[0,0],0),('i',[0,0],0),('p',[1,0],0),('z',[3,0,2],1),('i',[3,2,0],1),('i',[2,0,3,1],2),('p',[3,2,0],1)],
    'ones_positive':[('p',[1,0],0),('p',[2,2],0),('p',[3,2,0],1),('p',[0,3,1,0],2)],
}
MACRO_CASES['branch48_tail']=MACRO_CASES['ones_tail']
FAMILIES=list(MACRO_CASES)+['fold2','whole_zero_carry','marked_zero_carry','shrinking_increment']

def parameters(name):
    U=T.copy();fixed={};excluded={255};vary=(75,0);fuel=500
    if name=='delete255':fuel=2000
    elif name=='delete75':excluded={75};vary=(109,0)
    elif name in ('ones_tail','ones_positive'):
        fixed={(109,0):(1,1,75),(75,1):(1,-1,33)}
        if name=='ones_positive':fixed.pop((75,1));vary=(75,1)
    elif name=='branch48_tail':fixed={(48,0):(1,-1,131),(131,0):(0,1,7)}
    elif name=='fold2':
        U={k:(w,d,4 if q==2 else q) for k,(w,d,q) in U.items() if k[0]!=2}
        vary=(20,0);excluded=set();fuel=5000
    elif name in ('whole_zero_carry','marked_zero_carry'):
        U={k:v for k,v in U.items() if k[0] not in (112,131)}
        fixed={(255,1):(0,1,95)};vary=(255,0);excluded=set();fuel=10000
        if name=='marked_zero_carry':fixed[(75,0)]=(0,1,255)
    elif name=='shrinking_increment':
        U={k:v for k,v in U.items() if k[0] not in (75,255)}
        fixed={(109,0):(0,1,48),(48,0):(1,-1,131)}
        vary=(131,0);excluded=set();fuel=10000
    U.update(fixed)
    return U,fixed,vary,sorted({q for q,b in U}-excluded),fuel

def expected_for(name):
    def expected(pc,kind,r,regs,spares,head,span):
        if kind=='CD' and regs[chk.PHYSICAL[r]]==0:
            if name in ('whole_zero_carry','marked_zero_carry'):span+=1
            if name=='whole_zero_carry':spares=spares+[1]
        if kind=='CI' and name=='shrinking_increment':span-=1
        ans=RAW_EXPECTED(pc,kind,r,regs,spares,head,span)
        if kind=='CI' and name in ('marked_zero_carry','shrinking_increment'):
            h,one,p,s,rs,ss=ans;ss=ss[:-1]
            ans=h,chk.paint(p,s,rs,ss,h),p,s,rs,ss
        return ans
    return expected

def run_family(name):
    U,fixed,vary,states,fuel=parameters(name)
    macro=name in MACRO_CASES
    if macro:cases=MACRO_CASES[name]
    else:
        sites=chk.program_sites(BASE/'sources/Prog254.v')
        order=('CI','CD','CC','CB') if name=='fold2' else ('CD','CI','CC','CB')
        chosen=[next(s for s in sites if s[1]==kind) for kind in order]
        cases=[(pc,kind,r,z) for pc,kind,r in chosen for z in ((False,True) if kind=='CD' else (None,))]
        chk.expected=expected_for(name)
    began=time.monotonic();survivors=[];hist=Counter();first_failure=None;attempted=0
    for w in (0,1):
        for d in (-1,1):
            for q in states:
                U[vary]=(w,d,q);outcomes=[]
                for i,case in enumerate(cases):
                    attempted+=1
                    try:
                        if macro:
                            mode,values,r=case
                            answer=sim(U,mode,values,r,fuel=fuel)
                            if answer is None:raise AssertionError('local protocol did not reach its target')
                        else:
                            pc,kind,r,z=case;regs=[i*3%7 for i in range(9)]
                            if kind=='CD':regs[chk.PHYSICAL[r]]=int(z)
                            answer=chk.run_case(U,pc,kind,r,regs,[0],head=0,span=40,fuel=fuel)[0]
                        outcomes.append(answer)
                    except (AssertionError,KeyError) as exc:
                        hist[str(i)]+=1
                        if first_failure is None:first_failure=dict(action=[*vary,w,d,q],case_index=i,case=case,error=str(exc))
                        break
                else:survivors.append(dict(action=[*vary,w,d,q],outcomes=outcomes))
    chk.expected=RAW_EXPECTED
    return dict(status='completed_finite_screen',family=name,baseline_sha256=BASE_SHA256,
        varied_entry=list(vary),fixed_edits=[[*k,*v] for k,v in sorted(fixed.items())],
        recipes=4*len(states),case_runs=attempted,cases=cases,fuel=fuel,
        protocol=('Local macro target, arbitrary appendable valid spare blocks, exact prefix. '
                  'Stop on head<-1, exact repeated configuration, bad exit frame, or fuel.' if macro else
                  'Whole-tape literal instruction targets at dispatch96; at most15 intermediate dispatch visits.'),
        survivors=survivors,rejections_by_first_case=dict(hist),first_failure=first_failure,
        seconds=time.monotonic()-began,
        limitation='Finite screening only; no lower bound, unbounded equivalence, or consistency theorem.')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family',choices=FAMILIES+['all'],default='all')
    p.add_argument('--output-dir',type=Path,default=HERE/'reproduced-searches')
    args=p.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    for name in FAMILIES if args.family=='all' else [args.family]:
        result=run_family(name)
        (args.output_dir/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ('family','recipes','case_runs','survivors','seconds')}),flush=True)

if __name__=='__main__':main()
