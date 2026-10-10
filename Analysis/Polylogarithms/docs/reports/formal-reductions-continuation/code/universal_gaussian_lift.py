#!/usr/bin/env python3
"""Replay the universal same-point lift for cyclotomic imaginary product rows."""
from collections import defaultdict
from math import comb, gcd
from pathlib import Path
import argparse
import json
from full_gaussian_rank import transform, rational_rank

def canonical(N,a,r,s):
    r%=N;s%=N;inv=((-r)%N,(-s)%N)
    if (r,s)==inv:return None,0
    if (r,s)<inv:return (a,r,s),1
    return (a,*inv),-1

def raw(N,w):
    pairs=[(r,s) for r in range(N) for s in range(N)
           if (r,s)<((-r)%N,(-s)%N)]
    roots=list(range(1,(N+1)//2))
    cols=[(a,r,s) for a in range(1,w) for r,s in pairs
          if not(a==1 and r==0)]
    pos={v:j for j,v in enumerate(cols)};rows=[]
    def term(row,a,r,s,k):
        key,sgn=canonical(N,a,r,s)
        if sgn:
            row[key]+=sgn*k
            if not row[key]:del row[key]
    for p in range(1,w):
        q=w-p
        for r in range(N):
            for s in range(N):
                S=defaultdict(int);H=defaultdict(int)
                term(S,p,r,s,1);term(S,q,s,r,1)
                for j in range(p):term(H,q+j,s,r-s,comb(q+j-1,j))
                for j in range(q):term(H,p+j,r,s-r,comb(p+j-1,j))
                divs=(p==1 and r==0)+(q==1 and s==0)
                if divs==1:
                    for key,v in H.items():
                        S[key]-=v
                        if not S[key]:del S[key]
                    chosen=[S]
                elif divs==0:chosen=[S,H]
                else:chosen=[]
                for row in chosen:
                    if not row:continue
                    assert all(k in pos for k in row)
                    rr=[0]*len(cols)
                    for key,v in row.items():rr[pos[key]]=v
                    rows.append(rr)
    assert len(cols)==(N*N-gcd(N,2)**2)//2*(w-1)-len(roots)
    return rows,cols,roots

def lift(N,w,t,G,cols):
    n=w-2;c=G[n]
    U=[-v for v in transform(G,0,1,1,0)];U[0]+=c
    M=transform(G,1,-1,1,0)
    polys={(t,0):G,(0,t):U,(t,N-t):M}
    return [polys.get((r,s),[0]*(n+1))[a-1] for a,r,s in cols]

def verify(N,w,rank_check=False):
    rows,cols,roots=raw(N,w);vectors=[]
    if w%2:
        n=w-2
        for t in roots:
            for j in range((w-1)//2):
                h=n-2*j;G=[0]*(n+1)
                for k in range(h+1):G[2*j+k]=comb(h,k)*(-1)**k*2**(h-k)
                vectors.append(lift(N,w,t,G,cols))
        assert all(not any(sum(a*b for a,b in zip(row,v)) for row in rows)
                   for v in vectors)
    result={'level':N,'weight':w,'columns':len(cols),'rows':len(rows),
            'lift_basis_size':len(vectors),'all_lift_residuals_zero':True}
    if rank_check:
        ng=[j for j,(a,r,s) in enumerate(cols) if s!=0]
        rank=rational_rank(rows);rank_ng=rational_rank([[r[j] for j in ng] for r in rows])
        difference=rank-rank_ng
        predicted=len(roots)*((w-1)//2 if w%2 else w-1)
        assert difference==predicted
        result.update(rank=rank,nong_rank=rank_ng,rank_difference=difference)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('universal_gaussian_lift_results.json'))
    args=parser.parse_args()
    results=[verify(N,w,rank_check=True) for N in range(3,7) for w in (2,3,4)]
    results += [verify(N,w) for N in (3,4,5,6,8,10,12) for w in (5,9)]
    p=args.output
    p.write_text(json.dumps({'scope':'Formal imaginary single-product coefficient matrices, one-divergence difference rows only.',
        'checks':results},indent=2)+'\n')
    print(json.dumps({'output':str(p),'checks':results},indent=2))
