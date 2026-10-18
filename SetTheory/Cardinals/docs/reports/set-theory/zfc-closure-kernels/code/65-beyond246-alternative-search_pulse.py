#!/usr/bin/env python3
"""Reproduce a finite pulse255-deletion search with three/four unknown rows.

This is a bounded discovery search, not a macro proof or a lower bound.
Each candidate must hit all 48 complete-tape goals at ticks1 through249.
An endpoint reached at tick250 or later is outside this experiment.
"""
from pathlib import Path
import argparse,hashlib,json,time
HERE=Path(__file__).resolve().parent
BASE_PIN='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
TARGETS=(2,4,6,7,10,14,20,28,31,38,40,44,48,56,60,63,64,69,73,75,83,95,109,112,131)
FAMILIES=(
    [(75,0),(131,0),(131,1)],
    [(75,0),(112,0),(112,1)],
    [(75,0),(75,1),(131,0)],
    [(75,0),(75,1),(131,1)],
    [(75,0),(75,1),(131,0),(131,1)],
)

def table():
    raw=(HERE/'reference/context246_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==BASE_PIN
    t={}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,f=line.split();t[int(q),int(b)]=int(w),d,int(f)
    assert len(t)==492 and {q for q,b in t}=={q for q,b in t if b==0}
    return t

def blocks(values):
    out=[]
    for v in values:out += [0]+[1]*(v+1)
    return out

def marked(values,r):
    out=blocks(values);out[sum(v+2 for v in values[:r])+1]=0;return out

def paint(right,left,head):
    return {head+i for i,b in enumerate(right) if b}|{head-i-1 for i,b in enumerate(left) if b}

def fixtures(homogeneous):
    for vs in ([0]*10,[1]*10,[0,1,2,0,3,1,0,1,0,2],[2,0,1,2,0,1,2,0,1,0,3]):
        for r in (0,1,4,8):
            for mode in ('zero','pos','inc'):
                v=list(vs[:9])+[1]*(len(vs)-9) if homogeneous else list(vs)
                if mode=='zero':v[r]=0
                if mode=='pos':v[r]=max(1,v[r])
                want=list(v)
                if mode=='inc':want[r]+=1;want.append(1)
                if mode=='pos':want[r]-=1
                start=(73 if mode=='inc' else 95,0,paint(marked(v,r),[1,0,1],0))
                goal=(48 if mode!='zero' else 112,0 if mode=='pos' else -1,
                    paint(blocks(want),[1,1,0,1] if mode=='pos' else [1,0,1],1 if mode=='pos' else 0))
                yield start,goal

def partial(t,start,goal):
    q,h,one=start;qwant,hwant,owant=goal;one=set(one)
    for tick in range(250):
        if tick and q==qwant and h==hwant and one==owant:return True
        if q==254 or q==255:return False
        key=q,int(h in one)
        if t[key] is None:return key
        w,d,q=t[key]
        if w:one.add(h)
        else:one.discard(h)
        h+=1 if d=='R' else -1
    return False

def check_baseline(t,cases):
    # Baseline contains255. This separate total interpreter has the same
    # endpoint rule but does not reserve255 as the deleted state.
    for start,goal in cases:
        q,h,ones=start;ones=set(ones)
        for tick in range(250):
            if tick and (q,h,ones)==goal:break
            assert q!=254
            w,d,q=t[q,int(h in ones)]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=1 if d=='R' else -1
        else:raise AssertionError('baseline does not satisfy fixture')

def search(base,cases,holes):
    t={k:v for k,v in base.items() if k[0]!=255}
    for k in holes:t[k]=None
    actions=[(w,d,q) for q in TARGETS for w in (0,1) for d in ('L','R')]
    assert len(actions)==100
    solutions=[];examined=0;maxcase=0
    def descend(caseidx):
        nonlocal examined,maxcase
        maxcase=max(maxcase,caseidx)
        while caseidx<len(cases):
            answer=partial(t,*cases[caseidx]);examined+=1
            if answer is False:return
            if answer is True:caseidx+=1;continue
            # An unassigned row is intercepted before its first use. Earlier
            # successful traces therefore cannot depend on its future value.
            for action in actions:t[answer]=action;descend(caseidx)
            t[answer]=None;return
        solutions.append({str(k):t[k] for k in holes})
    descend(0)
    return dict(holes=holes,examined=examined,maxcase=maxcase,solutions=solutions)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--arbitrary-spares',action='store_true',help='Use the four original sampled spare patterns instead of allB1.')
    parser.add_argument('--baseline-only',action='store_true',help='Check the 48 finite baseline fixtures without synthesis.')
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions required; do not use -O.')
    baseline=table();cases=list(fixtures(not args.arbitrary_spares));assert len(cases)==48
    check_baseline(baseline,cases)
    if args.baseline_only:print('48 baseline fixtures PASS');return
    began=time.monotonic();results=[]
    for family in FAMILIES:
        row=search(baseline,cases,family);results.append(row);print(json.dumps(row),flush=True)
    name='pulse-search-arbitrary-spares.json' if args.arbitrary_spares else 'pulse-search-homogeneous.json'
    out=dict(status='COMPLETE',scope='Bounded synthesis screening; no new macro proof, machine endpoint or state lower bound.',
        table_sha256=BASE_PIN,deleted_state=255,spare_policy='original four sampled patterns' if args.arbitrary_spares else 'every fixture has only B(1) spares',
        fixture_count=48,target_states=list(TARGETS),actions_per_unknown_row=100,goal_ticks=[1,249],transition_limit=250,
        recipe_space_per_three_row_family=100**3,recipe_space_four_row_family=100**4,
        families=results,seconds=time.monotonic()-began)
    (HERE/'results'/name).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
