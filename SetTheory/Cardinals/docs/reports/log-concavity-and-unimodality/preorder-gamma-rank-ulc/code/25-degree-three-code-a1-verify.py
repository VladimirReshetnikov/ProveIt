#!/usr/bin/env python3
"""Independent certificate verification; standard library only, exact integers."""
import csv,json
from pathlib import Path
from collections import Counter
from math import comb
ROOT=Path(__file__).resolve().parent

def is_preorder(rows):
    r=[x|(1<<i)for i,x in enumerate(rows)]
    return all(not(r[j]&~r[i])for i in range(len(r))for j in range(len(r))if r[i]>>j&1)

def supports(rows):
    # Build endpoint-set pairs bottom-up from disjoint directed edges.
    # Sets identify supports, so several matchings never overcount a support.
    edges=[(1<<i,1<<j)for i,r in enumerate(rows)for j in range(len(rows))if r>>j&1]
    levels=[{(0,0)}]
    for k in range(1,len(rows)//2+1):
        levels.append({(a|x,b|y)for a,b in levels[-1]for x,y in edges if not((a|b)&(x|y))})
    return levels

def pair_for(rows,v):
    lev=supports(rows);p=[len(s)for s in lev]+[0]*4
    q=[sum(not((a|b)>>v&1)for a,b in s)for s in lev]+[0]*4
    if q[3]:return None
    return tuple(p[1:4]+q[1:3])

def proof(A,B,C):
    assert A>=0 and C>=0
    if B>=0:return 'nonnegative_coefficients',C
    assert A>0
    D=4*A*C-B*B
    assert D>=0
    # 4 A f(m) = (2 A m+B)^2+D, all real m.
    return 'completed_square',D

records=list(csv.DictReader((ROOT/'pairs.csv').open())); known=set(); proofs=[];summary=Counter()
for r in records:
    rows=tuple(map(int,r['rowmasks'].split()));v=int(r['v']);n=int(r['n'])
    assert len(rows)==n and 1<=n<=7 and 0<=v<n
    assert all(not(x>>i&1)for i,x in enumerate(rows)) and is_preorder(rows)
    assert all(not(x>>v&1)for x in rows) # singleton minimal vertex
    key=tuple(int(r[x])for x in ('p1','p2','p3','q1','q2'))
    assert pair_for(rows,v)==key,(r,pair_for(rows,v))
    assert key not in known;known.add(key)
    a,b,c,u,w=key
    if c==0:
        assert a*a>=4*b # actual degree two at m=0, when b>0
    if c==0 and w==0:
        kind,D=proof(1,2*a-4*u,a*a-4*b)
        summary['degree2_'+kind]+=1
        proofs.append([*key,'actual_degree2',1,2*a-4*u,a*a-4*b,kind,D])
    for name,(A,B,C) in [('first',(1,2*a-3*u,a*a-3*b)),('second',(u*u-3*w,2*b*u-3*a*w-3*c,b*b-3*a*c))]:
        kind,D=proof(A,B,C);summary[name+'_'+kind]+=1
        proofs.append([*key,name,A,B,C,kind,D])
summary['unique_pairs']=len(known);summary['valid_marked_expansions']=sum(int(r['count'])for r in records)
print('All stored representatives independently reconstructed and all-m gaps certified',dict(summary),flush=True)

# Independent quotient-poset generator: extend by a final maximal vertex,
# choosing its strict predecessor set to be an ideal of the old poset.
qs=[()];qcounts=[]
for n in range(1,8):
    nxt=[]
    for old in qs:
        k=len(old);pred=[sum(1<<i for i in range(k)if old[i]>>j&1)for j in range(k)]
        for mask in range(1<<k):
            if all(not(pred[j]&~mask)for j in range(k)if mask>>j&1):
                nxt.append(tuple(r|((1<<k)if mask>>i&1 else 0)for i,r in enumerate(old))+(0,))
    qs=nxt;qcounts.append(len(qs))
assert qcounts==[1,2,7,40,357,4824,96428],qcounts
expansions=[sum(qcounts[k-1]*comb(n-1,k-1)for k in range(1,n+1))for n in range(1,8)]
assert expansions==[1,3,12,68,568,7090,131645]
summary['quotient_counts']=qcounts;summary['expanded_core_counts']=expansions
print('Independent ideal-extension quotient counts:',qcounts,flush=True)

# Direct unrelated enumeration of ALL directed relations through four vertices.
# This tests preorder transitivity, marks, and support pairs without quotienting.
direct_counts=[];direct_marks=[]
for n in range(1,5):
    es=[(i,j)for i in range(n)for j in range(n)if i!=j];count=marks=0
    for mask in range(1<<len(es)):
        rows=[0]*n
        for e,(i,j)in enumerate(es):
            if mask>>e&1:rows[i]|=1<<j
        if not is_preorder(rows):continue
        count+=1
        for v in range(n):
            if all(not(r>>v&1)for r in rows):
                key=pair_for(rows,v);assert key in known;marks+=1
    direct_counts.append(count);direct_marks.append(marks)
assert direct_counts==[1,4,29,355]
summary['direct_labeled_preorder_counts']=direct_counts;summary['direct_labeled_minimal_marks']=direct_marks
summary['all_passed']=True
with (ROOT/'quadratic_certificates.csv').open('w')as f:
    out=csv.writer(f);out.writerow(['p1','p2','p3','q1','q2','gap','A','B','C','certificate','nonnegative_remainder']);out.writerows(proofs)
(ROOT/'verification.json').write_text(json.dumps(dict(summary),indent=2)+'\n')
print('Direct labeled enumeration and all checks passed',flush=True)
