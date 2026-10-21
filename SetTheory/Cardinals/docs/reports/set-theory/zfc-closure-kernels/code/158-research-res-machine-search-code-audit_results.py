#!/usr/bin/env python3
"""Independently enumerate family sizes and check stored search accounting.

This is an accounting/domain audit, not a second execution of every rejected
candidate. The complete bounded searches can be repeated by reproduce.py.
"""
from pathlib import Path
from collections import deque
import hashlib,json,time
import check_joint_fold as checker
from reproduce import SEEDS

ROOT=Path(__file__).resolve().parent.parent
PIN='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'

def blank_domain(table,start,radius):
    mask=(1<<(2*radius+1))-1
    inv={q:set()for q,b in table};inv[254]=set()
    inv[start].add(0);todo=deque([(start,0)])
    def post(q,m):
        w,d,z=table[q,(m>>radius)&1];x=(m&~(1<<radius))|(w<<radius)
        if d==1:a=x>>1;return z,(a,a|(1<<(2*radius)))
        a=(x<<1)&mask;return z,(a,a|1)
    while todo:
        q,m=todo.popleft()
        if q==254:continue
        z,patterns=post(q,m)
        for n in patterns:
            if n not in inv[z]:inv[z].add(n);todo.append((z,n))
    for q in inv:
        if q==254:continue
        for m in inv[q]:
            z,patterns=post(q,m)
            if not all(n in inv[z]for n in patterns):raise ValueError('Noninductive blank-window domain')
    if 0 not in inv[start]:raise ValueError('Blank initial context absent')
    return inv

def main():
    began=time.monotonic();p=ROOT/'inputs/k218.native.tm'
    if hashlib.sha256(p.read_bytes()).hexdigest()!=PIN:raise ValueError('Input pin mismatch')
    T,start=checker.read(p);Q=sorted({q for q,b in T})
    full=checker.domain(T,start,7);blank=blank_domain(T,start,7)
    narrowed={q for q in Q if blank[q]!=full[q]}
    if narrowed!={0,4,40,54,66,94,97,113,198}:raise ValueError('Narrowed-state family differs')
    equal=[(keep,drop)for i,keep in enumerate(Q)for drop in Q[i+1:]]
    shifted=[]
    for keep in Q:
        for drop in Q:
            if keep==drop or drop==start:continue
            for delta in(-2,2):
                if all(d+delta in(-1,1)for(q,b),(w,d,z)in T.items()if q not in(keep,drop)and z==drop):
                    shifted.append((keep,drop,delta))
    families={
        'full-two-row-v2':equal,
        'full-shifted-v2':shifted,
        'blank-two-row':[pair for pair in equal if narrowed.intersection(pair)],
        'blank-shifted':[pair for pair in shifted if narrowed.intersection(pair[:2])],
    }
    for seed,stem in [('row157','full-two-row-row157'),('contextual','full-two-row-contextual'),('contextual_row157','full-two-row-contextual-row157')]:
        filename,pin=SEEDS[seed];table_path=ROOT/'inputs'/filename
        if hashlib.sha256(table_path.read_bytes()).hexdigest()!=pin:raise ValueError('Alternate input pin mismatch')
        other,_=checker.read(table_path);states=sorted({q for q,b in other})
        families[stem]=[(keep,drop)for i,keep in enumerate(states)for drop in states[i+1:]]
    families['observed']=equal
    families['observed-shifted-long']=shifted
    for stem,pairs in [('observed-wide',equal),('observed-shifted-wide',shifted)]:
        if(ROOT/'evidence'/(stem+'-result.json')).exists():families[stem]=pairs
    records=[]
    for name,pairs in families.items():
        r=json.loads((ROOT/'evidence'/(name+'-result.json')).read_text());arity=4*len(Q)
        if r['status']not in('COMPLETE','TIME_LIMIT') or r['hits']!=0:raise ValueError('Unexpected receipt status')
        if r['status']=='COMPLETE':
            if r['pairs']!=len(pairs) or r['covered_rejections']!=len(pairs)*arity**2:raise ValueError('Completed family not covered by recorded counts')
        elif not(1<=r['pairs']<=len(pairs)and(r['pairs']-1)*arity**2<=r['covered_rejections']<r['pairs']*arity**2):
            raise ValueError('Partial sequential prefix count is inconsistent')
        p0,p1,p2=r['pruned_depths']
        if p0*arity**2+p1*arity+p2!=r['covered_rejections']:raise ValueError('Pruning-account mismatch')
        if p0+p1+p2!=r['rejection_leaves']:raise ValueError('Rejection-account mismatch')
        internal=r['partial_checks']-r['rejection_leaves']
        if r['status']=='COMPLETE'and r['partial_checks']!=len(pairs)+arity*internal:raise ValueError('Complete branching-tree count mismatch')
        records.append(dict(family=name,status=r['status'],eligible_pair_specifications=len(pairs),
                            started_pair_specifications=r['pairs'],actions_per_row=arity,
                            assignments_in_entire_family=len(pairs)*arity**2,
                            rejected_complete_assignments=r['covered_rejections'],accounting='PASS'))
    result=dict(status='INDEPENDENT_FAMILY_AND_DOMAIN_ACCOUNTING_PASS',families=records,
                all_tape_contexts=sum(len(full[q])for q in Q),
                blank_window_contexts=sum(len(blank[q])for q in Q),
                narrowed_states=sorted(narrowed),seconds=time.monotonic()-began,
                scope='Independent enumeration of finite families, exact receipt arithmetic, and both inductive domains. Does not replay candidate rejection trajectories or prove any lower bound.')
    (ROOT/'evidence/accounting-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
