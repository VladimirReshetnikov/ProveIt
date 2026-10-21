#!/usr/bin/env python3
"""Bounded, soundly screened local state-fold synthesis (not a proof of optimality).

All initial tapes, start control 0. Window automaton overapproximates actual
runs: shifted-in bits are nondeterministic. A candidate macro is checked on
every admitted window; it may inspect only the represented cells. This finite
check supports a stuttering simulation at actual boundaries. No search
survivor is by itself called a consistency machine.
"""
from collections import defaultdict, deque
from pathlib import Path
from itertools import combinations
import json, argparse, time

def parse(p):
    t={}; start=0
    for line in Path(p).read_text().splitlines():
        if line.startswith('#! start '):start=int(line[9:])
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return start,t

def abstract(t,start,k):
    width=2*k+1;mask=(1<<width)-1
    seen=defaultdict(set);seen[start]=set(range(1<<width))
    todo=deque((start,v)for v in seen[start]);iterations=0
    while todo:
        q,v=todo.popleft();iterations+=1
        row=t.get((q,(v>>k)&1))
        if row is None:continue
        w,d,z=row
        v=(v&~(1<<k))|(w<<k)
        if d==1: a=v>>1; b=a|(1<<(width-1))
        else:a=(v<<1)&mask;b=a|1
        for u in [a,b]:
            if u not in seen[z]:seen[z].add(u);todo.append((z,u))
    return seen,iterations

def candidate_check(t,windows,k,a,b,sym,write,direct,provider,limit):
    # b is removed; a survives. Only one new row; other targets project b to a.
    phi=lambda q:a if q==b else q
    def row(q,c):
        if q==b:return None
        if(q,c)==(a,sym):return write,direct,provider
        r=t.get((q,c))
        return None if r is None else(r[0],r[1],phi(r[2]))
    summaries=[]
    for oldq in [a,b]:
        for bits in windows[oldq]:
            if (bits>>k)&1!=sym:continue
            ow,od,oz=t[oldq,sym];target=(phi(oz),od,(bits&~(1<<k))|(ow<<k))
            q=a;h=0;v=bits;found=False
            for n in range(1,limit+1):
                if not -k<=h<=k:break
                r=row(q,(v>>(h+k))&1)
                if r is None:break
                w,d,q=r;v=(v&~(1<<(h+k)))|(w<<(h+k));h+=d
                if(q,h,v)==target:
                    summaries.append(n);found=True;break
            if not found:return None
    return {'cases':len(summaries),'max_duration':max(summaries,default=0),'min_duration':min(summaries,default=0)}

def search(path,k,limit,out):
    start,t=parse(path);states=sorted({q for q,b in t});begin=time.time()
    windows,n=abstract(t,start,k)
    groups=[defaultdict(list),defaultdict(list)]
    for q in states:
        for c in [0,1]:groups[c][t[q,c]].append(q)
    attempts=0;survivors=[];pairs=0
    for common in [0,1]:
        sym=1-common
        for members in groups[common].values():
            for a,b in combinations(members,2):
                if b==start:a,b=b,a
                pairs+=1
                # Need direct transition equality after projection, automatic here.
                # Fold current bit's branch by a two-way move to an existing fragment.
                for w in [0,1]:
                    for d in [-1,1]:
                        for p in states:
                            if p==b:continue
                            attempts+=1
                            z=candidate_check(t,windows,k,a,b,sym,w,d,p,limit)
                            if z is not None:
                                survivors.append({'keep':a,'remove':b,'read':sym,'new':[w,d,p],**z})
                if pairs%25==0:print('progress',pairs,attempts,len(survivors),flush=True)
    result={'machine':str(path),'radius':k,'step_bound':limit,'abstract_states':n,'pairs':pairs,'attempts':attempts,'survivors':survivors,'seconds':time.time()-begin,'scope':'Only identical-common-branch pair merges, one replaced retained row, existing provider, bounded local macros on all reachable abstract windows. No minimality claim.'}
    Path(out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('machine');p.add_argument('--radius',type=int,default=2);p.add_argument('--steps',type=int,default=24);p.add_argument('--out',default='window-search.json');a=p.parse_args();search(a.machine,a.radius,a.steps,a.out)
