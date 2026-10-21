#!/usr/bin/env python3
"""Universal joint rewrite/fold audit by positive common-endpoint diagrams.

Independent of discovery code. Every original invariant context is checked.
Unknown exterior cells are arbitrary; blocks must join before reading outside
the window, and complete-window equality implies complete-tape equality.
"""
from pathlib import Path
from collections import deque,Counter
import argparse,hashlib,json,time

def need(ok,message):
    if not ok:raise ValueError(message)

def read(path):
    T={};start=None
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
        T[q,b]=(w,1 if d=='R'else-1,z)
    Q={q for q,b in T}
    need(set(T)=={(q,b)for q in Q for b in(0,1)},'table is not total')
    need(start in Q and 254 not in Q,'bad start/halt')
    need(all(z in Q|{254}for w,d,z in T.values()),'undefined successor')
    return T,start

def domain(T,start,radius):
    width=2*radius+1;mask=(1<<width)-1
    Q={q for q,b in T};I={q:set()for q in Q|{254}}
    I[start].add(0);todo=deque([(start,0)])
    def post(q,m):
        w,d,z=T[q,(m>>radius)&1];x=(m&~(1<<radius))|(w<<radius)
        if d==1:a=x>>1;return z,(a,a|(1<<(width-1)))
        a=(x<<1)&mask;return z,(a,a|1)
    while todo:
        q,m=todo.popleft()
        if q==254:continue
        z,patterns=post(q,m)
        for n in patterns:
            if n not in I[z]:I[z].add(n);todo.append((z,n))
    need(0 in I[start],'blank initial window omitted')
    for q in Q:
        for m in I[q]:
            z,patterns=post(q,m)
            need(all(n in I[z]for n in patterns),'window invariant is not inductive')
    return I

def check(O,N,oldstart,newstart,keep=None,drop=None,radius=5,fuel=97,I=None):
    Q={q for q,b in O};R={q for q,b in N}
    need((keep is None)==(drop is None),'incomplete state map')
    if drop is None:phi=lambda q:q;need(Q==R,'identity rewrite changed state set')
    else:
        need(drop in Q and keep in R and drop!=keep,'invalid fold states')
        need(R==Q-{drop},'fold changed wrong state set')
        phi=lambda q:keep if q==drop else q
    need(phi(oldstart)==newstart,'initial states do not correspond')
    if I is None:I=domain(O,oldstart,radius)
    hist=Counter();contexts=0;changed=[];checked=0
    def step(T,q,h,m):
        b=(m>>(h+radius))&1;w,d,z=T[q,b]
        return z,h+d,(m&~(1<<(h+radius)))|(w<<(h+radius))
    for q in sorted(Q):
        for b in(0,1):
            w,d,z=O[q,b];newrow=N[phi(q),b]
            patterns=[m for m in I[q]if((m>>radius)&1)==b]
            contexts+=len(patterns)
            if newrow==(w,d,phi(z)):
                hist[1,1]+=len(patterns);continue
            changed.append([q,b]);checked+=len(patterns)
            for m in sorted(patterns):
                goals={};oq,oh,om=q,0,m;old_halt=None
                for oldn in range(1,fuel+1):
                    if oq==254 or not -radius<=oh<=radius:break
                    oq,oh,om=step(O,oq,oh,om)
                    if oq==254:old_halt=oldn
                    goals.setdefault((phi(oq),oh,om),oldn)
                nq,nh,nm=phi(q),0,m
                for newn in range(1,fuel+1):
                    need(nq!=254 and -radius<=nh<=radius,
                         f'new run exits before join: old row {(q,b)}, window {m}')
                    nq,nh,nm=step(N,nq,nh,nm)
                    if nq==254:
                        need(old_halt is not None,
                             f'new halt without proved old halt: {(q,b)}, window {m}')
                        hist[old_halt,newn]+=1;break
                    oldn=goals.get((nq,nh,nm))
                    if oldn is not None:hist[oldn,newn]+=1;break
                else:raise ValueError(f'no positive common endpoint: {(q,b)}, window {m}')
    need(sum(hist.values())==contexts,'context accounting mismatch')
    return dict(status='INDEPENDENT_BLANK_WINDOW_JOINT_DIAGRAM_PASS',
                old_states=len(Q),new_states=len(R),start_old=oldstart,start_new=newstart,
                keep=keep,drop=drop,radius=radius,fuel=fuel,
                inductive_window_contexts=contexts,nontrivial_contexts=checked,
                changed_old_rows=changed,
                positive_old_new_block_histogram=[[a,b,n]for(a,b),n in sorted(hist.items())],
                maximum_old_block=max(a for a,b in hist),maximum_new_block=max(b for a,b in hist),
                scope='All tapes whose radius-window at the initial head is zero, hence blank tape. The original window invariant is independently recomputed and checked inductive. Every original invariant configuration has strictly positive old/new blocks ending in mapped identical state, head, and entire tape, or both halt. No block reads outside its universally quantified finite window before joining. Positive uniformly bounded blocks give halting equivalence, not merely bounded-run agreement.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True)
    ap.add_argument('--new',type=Path,required=True);ap.add_argument('--keep',type=int)
    ap.add_argument('--drop',type=int);ap.add_argument('--radius',type=int,default=5)
    ap.add_argument('--fuel',type=int,default=97);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();now=time.monotonic();O,os=read(a.old);N,ns=read(a.new)
    I=domain(O,os,a.radius);out=check(O,N,os,ns,a.keep,a.drop,a.radius,a.fuel,I)
    bad=N.copy();bad[ns,0]=(0,1,254)
    try:check(O,bad,os,ns,a.keep,a.drop,a.radius,a.fuel,I)
    except ValueError as e:out['negative_control']={'status':'REJECTED','reason':str(e)}
    else:raise ValueError('corrupt initial halt was accepted')
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    out.update(old_sha256=sha(a.old),new_sha256=sha(a.new),checker_sha256=sha(Path(__file__)),
               seconds=time.monotonic()-now)
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
