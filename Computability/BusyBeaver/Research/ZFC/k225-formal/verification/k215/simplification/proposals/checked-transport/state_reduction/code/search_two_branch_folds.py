#!/usr/bin/env python3
"""Exact three-transition folds allowing BOTH differing read branches.

All candidate soundness obligations are finite premises of a stuttering
simulation on an inductive finite-window overapproximation.  Failure is scoped
to this explicitly defined template; it is not a Turing-machine lower bound.
"""
from pathlib import Path
from collections import deque,Counter
import argparse,itertools,json,hashlib,time

def parse(path):
    T={};start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    S=sorted({q for q,b in T}); assert len(T)==2*len(S)
    H={z for w,d,z in T.values()}-set(S);assert len(H)==1
    return T,S,start,next(iter(H))

def windows(T,S,start,halt,radius):
    width=2*radius+1;mask=(1<<width)-1
    sets={q:set() for q in S+[halt]};sets[start]=set(range(1<<width))
    todo=deque((start,x)for x in sets[start])
    while todo:
        q,x=todo.popleft()
        if q==halt:continue
        b=(x>>radius)&1;w,d,z=T[q,b]
        y=(x&~(1<<radius))|(w<<radius)
        if d==1: ys=(y>>1,(y>>1)|(1<<(width-1)))
        else: ys=((y<<1)&mask,((y<<1)&mask)|1)
        for y in ys:
            if y not in sets[z]:sets[z].add(y);todo.append((z,y))
    return sets

def serialize(T,start):
    return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z)in sorted(T.items()))).encode()

def search(path,radius,outdir):
    raw=path.read_bytes();T,S,start,halt=parse(path);W=windows(T,S,start,halt,radius)
    domains={(q,b,d):{(x>>(radius-d))&1 for x in W[q] if((x>>radius)&1)==b}for q in S for b in(0,1)for d in(-1,1)}
    pair_count=0;both_differ=0;branch_pass=Counter();solutions=[]
    # q is the retained state; both retention choices are covered.
    for q,r in itertools.permutations(S,2):
        if r==start:continue
        phi=lambda z:q if z==r else z
        if any(T[q,b][:2]!=T[r,b][:2]for b in(0,1)):continue
        pair_count+=1
        if all(phi(T[q,b][2])!=phi(T[r,b][2])for b in(0,1)):both_differ+=1
        choices=[]
        for b in(0,1):
            w,d,_=T[q,b];c=[]
            if phi(T[q,b][2])==phi(T[r,b][2]):c.append({'kind':'direct','action':(w,d,phi(T[q,b][2]))})
            for h in S:
                if h in(q,r):continue
                good=True;cases=[]
                for old in(q,r):
                    for m in domains[old,b,d]:
                        wh,dh,s=T[h,m]
                        if(wh,dh)!=(m,d)or s in(q,r,halt):good=False;break
                        ws,ds,t=T[s,w]
                        if(ws,ds,phi(t))!=(w,d,phi(T[old,b][2])):good=False;break
                        cases.append([old,m,h,s,phi(t)])
                    if not good:break
                if good:c.append({'kind':'three_step','action':(w,-d,h),'cases':cases})
            choices.append(c)
        branch_pass[str(tuple(bool(c)for c in choices))]+=1
        if all(choices):
            for cs in itertools.product(*choices):
                N={(z,b):(w,d,phi(t))for(z,b),(w,d,t)in T.items()if z!=r}
                for b,c in enumerate(cs):N[q,b]=c['action']
                nr=serialize(N,start);sid=len(solutions)
                record={'keep':q,'drop':r,'branches':cs,'new_sha256':hashlib.sha256(nr).hexdigest(),'states':len(N)//2}
                solutions.append(record)
                (outdir/f'candidate_{sid:03d}.native.tm').write_bytes(nr)
    return {'table':str(path),'sha256':hashlib.sha256(raw).hexdigest(),'radius':radius,'window_count':sum(map(len,W.values())),
            'pair_retention_choices':pair_count,'both_target_branches_differ':both_differ,'branch_pass':dict(branch_pass),'solutions':solutions}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--radius',type=int,default=3);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    started=time.monotonic();res=search(a.table,a.radius,a.output);res['seconds']=time.monotonic()-started
    res['status']='EXACT_TEMPLATE_FOLD_FOUND'if res['solutions']else'NO_FOLD_IN_TWO_BRANCH_THREE_STEP_TEMPLATE'
    res['scope']=__doc__;res['code_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (a.output/'result.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
if __name__=='__main__':main()
