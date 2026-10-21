#!/usr/bin/env python3
"""Finite local-context overapproximation for all-tape-from-start rewrites.

Search only: absence of a result is not a lower bound. A successful block is
universally exact on every context in an inductive reachability overapproximation.
"""
from pathlib import Path
from collections import deque
import argparse,itertools,json,time,hashlib
import build221 as b

def contexts(T,start,radius):
    width=2*radius+1;mask=(1<<width)-1;cur=1<<radius
    C={q:set() for q,_ in T};queue=deque()
    for m in range(1<<width): C[start].add(m);queue.append((start,m))
    while queue:
        q,m=queue.popleft();bit=(m>>radius)&1
        w,d,z=T[q,bit]
        if z not in C:continue
        a=(m|cur) if w else (m&~cur)
        if d==1:base=a>>1;newbit=1<<(width-1)
        else:base=(a<<1)&mask;newbit=1
        for n in (base,base|newbit):
            if n not in C[z]:C[z].add(n);queue.append((z,n))
    return C

def block(T,q,m,radius,action,target,write,move,forbid,limit=63):
    """Exact whole-tape block if no unknown cell is read or modified."""
    tape={i-radius:(m>>i)&1 for i in range(2*radius+1)}
    expected=dict(tape);expected[0]=write
    h=0;state=q;seen=set();used=set()
    for tick in range(limit+1):
        if tick and h==move and state==target and tape==expected:return tick,used
        if h not in tape or tick==limit:return None
        key=(state,h,tuple(tape.values()))
        if key in seen:return None
        seen.add(key)
        if tick:
            if state in forbid:return None
            row=(state,tape[h]);used.add(row)
            if row not in T:return None
            w,d,state=T[row]
        else:w,d,state=action
        tape[h]=w;h+=d
    return None

def search(T,C,radius,limit):
    states=sorted(C);pairs=[];survivors=[];tried=0
    for q,r in itertools.combinations(states,2):
        if q==0 or r==0:continue
        for bit in (0,1):
            if T[q,1-bit]!=T[r,1-bit] or T[q,bit]==T[r,bit]:continue
            if T[q,bit][:2]!=T[r,bit][:2]:continue
            pairs.append([q,r,bit])
            for helper in states:
                if helper in (q,r):continue
                w,d,_=T[q,bit]
                for marker_dir in (-1,1):
                    # Preserve current symbol until the provider restores the required action.
                    action=(bit,marker_dir,helper);tried+=1;good=True;dur=set();used=set()
                    for z in (q,r):
                        target=T[z,bit][2]
                        if target in (q,r):good=False;break
                        for m in sorted(C[z]):
                            if ((m>>radius)&1)!=bit:continue
                            a=block(T,z,m,radius,action,target,w,d,{q,r},limit)
                            if a is None:good=False;break
                            dur.add(a[0]);used.update(a[1])
                        if not good:break
                    if good:
                        survivors.append(dict(keep=q,drop=r,bit=bit,action=action,durations=sorted(dur),used=sorted(used)))
    return dict(pairs=pairs,tried=tried,survivors=survivors)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--radius',type=int,default=3);ap.add_argument('--limit',type=int,default=63);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    t=time.monotonic();T=b.read_table(a.table.read_bytes());C=contexts(T,0,a.radius)
    ans=search(T,C,a.radius,a.limit)
    ans.update(radius=a.radius,limit=a.limit,context_counts={q:len(m)for q,m in C.items()},context_total=sum(map(len,C.values())),seconds=time.monotonic()-t,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),scope=__doc__)
    a.output.write_text(json.dumps(ans,indent=2)+'\n')
    print(json.dumps({k:v for k,v in ans.items()if k not in('pairs','context_counts','scope')},indent=2))
if __name__=='__main__':main()
