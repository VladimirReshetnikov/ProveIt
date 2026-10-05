#!/usr/bin/env python3
"""Independent exact checks of generalized Catalan first-pattern-failure counts.

No third-party packages required.  Three independent constructions are compared:
(1) direct pattern inspection of all permutations through size 9;
(2) minimum-insertion dynamic programming with first-failure and suffix states;
(3) exact coefficient extraction from the proposed rational-Catalan formula.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations
from math import comb
import argparse
import csv
import json
from pathlib import Path
import time


def catalan(n):
    return comb(2*n,n)//(n+1)


def avoids_123(p):
    # Streaming longest-increasing-subsequence threshold, independent of insertion.
    first = second = len(p)+1
    for a in p:
        if a > second:
            return False
        if a > first:
            second = min(second, a)
        else:
            first = a
    return True


def first_failure_literal(p, r, index_sets=None):
    """Inspect literal (r+1)-subsequences; tau=1,(r+1),r,...,2."""
    n = len(p)
    largest_minimum = 0
    for ids in index_sets if index_sets is not None else combinations(range(n), r+1):
        if p[ids[0]] >= p[ids[-1]]:
            continue
        if all(p[ids[a]] > p[ids[a+1]] for a in range(1,r)):
            largest_minimum = max(largest_minimum,p[ids[0]])
    return n-largest_minimum if largest_minimum else n


def brute_rows(max_n, rs):
    rows = {r: {} for r in rs}
    inspected = 0
    accepted = 0
    for n in range(1,max_n+1):
        inds = {r:list(combinations(range(n),r+1)) for r in rs}
        counts = {r:Counter() for r in rs}
        naccepted=0
        for p in permutations(range(1,n+1)):
            inspected += 1
            if not avoids_123(p):
                continue
            naccepted+=1
            for r in rs:
                counts[r][first_failure_literal(p,r,inds[r])]+=1
        assert naccepted == catalan(n), (n,naccepted,catalan(n))
        accepted+=naccepted
        for r in rs:
            rows[r][n]=[counts[r][k] for k in range(n+1)]
    return rows,dict(permutations_inspected=inspected,avoiding_permutations=accepted)


def state_dp(max_n,r):
    """Tree DP tracking suffix d and failure k; k=0 means still safe."""
    states={(1,0):1}
    rows={1:[0,1]}
    for size in range(1,max_n):
        nxt=defaultdict(int)
        for (d,k),count in states.items():
            # Insert a minimum at each active site, indexed by right-hand length j.
            for j in range(d+1):
                new_d=d+1 if j==0 else j
                new_k=k if k else (size if j>=r else 0)
                nxt[(new_d,new_k)]+=count
        states=nxt
        row=[0]*(size+2)
        for (_,k),count in states.items():
            row[k or size+1]+=count
        rows[size+1]=row
    return rows


def safe_state_dp(max_n,r):
    """Independent safe-only matrix evolution and tail counts."""
    states=[0,1]
    rows={1:states[:]}
    for size in range(1,max_n):
        nxt=[0]*(size+2)
        for d in range(1,size+1):
            nxt[d+1]+=states[d]
            for j in range(1,min(d,r-1)+1):
                nxt[j]+=states[d]
        states=nxt
        rows[size+1]=states[:]
    return rows


def D_coeffs(r):
    return [(-1)**j*comb(r+1-j,j) for j in range((r+1)//2+1)]


def reciprocal_coeffs(d,max_n):
    out=[1]
    for n in range(1,max_n+1):
        out.append(-sum(d[j]*out[n-j] for j in range(1,min(n,len(d)-1)+1)))
    return out


def ballot(m,p):
    # [x^m] C(x)^p, expressed without rational arithmetic.
    if m<0:
        return 0
    return comb(2*m+p-1,m)-(comb(2*m+p-1,m-1) if m else 0)


def gf_rows(max_n,r):
    d=D_coeffs(r)
    e=D_coeffs(r-2)
    q=reciprocal_coeffs(d,max_n)
    safe=[0]+[sum(e[j]*q[n-1-j] for j in range(min(n-1,len(e)-1)+1))
              for n in range(1,max_n+1)]
    rows={}
    for n in range(1,max_n+1):
        row=[0]*(n+1)
        row[n]=safe[n]
        for k in range(r,n):
            row[k]=sum(q[k-j]*ballot(n-k-1,j+1) for j in range(r,k+1))
        rows[n]=row
    return rows,q,safe


def recurrence_rows(max_n,r):
    """O(r N^2) exact recurrence from multiplication by D_r(xy)."""
    d=D_coeffs(r)
    e=D_coeffs(r-2)
    rows={0:[0]}
    for n in range(1,max_n+1):
        row=[0]*(n+1)
        for k in range(1,n+1):
            value=0
            for j in range(1,min(n,k,len(d)-1)+1):
                value-=d[j]*rows[n-j][k-j]
            if n==k and k-1<len(e):
                value+=e[k-1]
            elif n>k>=r:
                value+=ballot(n-k-1,k+1)
            row[k]=value
        rows[n]=row
    del rows[0]
    return rows


def conv(a,b,N):
    out=[0]*(N+1)
    for i,x in enumerate(a):
        if not x:
            continue
        for j,y in enumerate(b[:N+1-i]):
            out[i+j]+=x*y
    return out


def literal_gf_specializations(max_n,r,ys):
    """Expand entire univariate F_r(x,y) at integral y, independently of ballot."""
    C=[catalan(n) for n in range(max_n+1)]
    Cp=[1]+[0]*max_n
    for _ in range(r+1):
        Cp=conv(Cp,C,max_n)
    out={}
    d=D_coeffs(r)
    e=D_coeffs(r-2)
    for y in ys:
        invD=reciprocal_coeffs([dj*y**j for j,dj in enumerate(d)],max_n)
        invCatalan=reciprocal_coeffs([1]+[-y*C[n-1] for n in range(1,max_n+1)],max_n)
        diag_num=[0]+[ej*y**(j+1) for j,ej in enumerate(e)]
        diag=conv(diag_num,invD,max_n)
        post=conv(conv(Cp,invD,max_n),invCatalan,max_n)
        full=[diag[n]+(y**r*post[n-r-1] if n>=r+1 else 0)
              for n in range(max_n+1)]
        out[y]=full
    return out


def verify(max_brute=9,max_dp=40,max_safe=120,rs=tuple(range(2,7)),outdir=None):
    start=time.monotonic()
    brute,stats=brute_rows(max_brute,rs)
    records=[]
    checks=Counter()
    sample={}
    for r in rs:
        gf,q,safe=gf_rows(max_safe,r)
        dp=state_dp(max_dp,r)
        sdp=safe_state_dp(max_safe,r)
        rec=recurrence_rows(max_safe,r)
        specs=literal_gf_specializations(max_dp,r,(0,1,2,3,-1))
        for n in range(1,max_safe+1):
            row=gf[n]
            assert sum(row)==catalan(n),("row sum",r,n,row)
            checks['catalan_row_sums']+=1
            assert row==rec[n],('exact recurrence',r,n)
            checks['exact_recurrence_rows']+=1
            assert row[n]==sum(sdp[n]),("diagonal",r,n)
            checks['safe_diagonal']+=1
            assert row[n]==(catalan(n) if n<=r else row[n])
            if n>r:
                assert all(row[k]>0 for k in range(r,n))
            assert all(row[k]==0 for k in range(min(r,n)))
            checks['support']+=1
            if n>=r:
                for j in range(r,n+1):
                    assert sum(sdp[n][j:])==q[n-j],("safe tail",r,n,j)
                    checks['safe_tail_coefficients']+=1
            if n>r:
                # Earliest nonzero column has no r-dependence beyond Catalan power.
                assert row[r]==ballot(n-r-1,r+1)
                checks['first_nonzero_column']+=1
            if n<=max_dp:
                assert row==dp[n],("state DP",r,n,row,dp[n])
                checks['state_dp_rows']+=1
                for y,coeffs in specs.items():
                    assert sum(row[k]*y**k for k in range(n+1))==coeffs[n],(
                        "GF specialization",r,n,y)
                    checks['literal_gf_specializations']+=1
            if n<=max_brute:
                assert row==brute[r][n],("brute",r,n,row,brute[r][n])
                checks['literal_permutation_rows']+=1
            if n<=12:
                records.extend(dict(r=r,n=n,k=k,count=row[k]) for k in range(1,n+1))
        sample[str(r)]={str(n):gf[n][1:] for n in range(1,11)}
    summary=dict(status='PASS',r_values=list(rs),max_brute=max_brute,max_dp=max_dp,
                 max_safe=max_safe,elapsed_seconds=round(time.monotonic()-start,3),
                 checks=dict(checks),brute=stats,sample_rows=sample)
    if outdir:
        outdir=Path(outdir)
        outdir.mkdir(parents=True,exist_ok=True)
        (outdir/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        with (outdir/'exact_small_tables.csv').open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=['r','n','k','count'])
            w.writeheader();w.writerows(records)
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--brute',type=int,default=9)
    parser.add_argument('--dp',type=int,default=40)
    parser.add_argument('--safe',type=int,default=120)
    parser.add_argument('--outdir',default=str(Path(__file__).resolve().parents[1]/'data'))
    parser.add_argument('--skip-limits',action='store_true',help='Skip additional limit-law audit')
    args=parser.parse_args()
    summary=verify(args.brute,args.dp,args.safe,outdir=args.outdir)
    if not args.skip_limits:
        from audit_limit_laws import run as audit_limits
        limit_summary=audit_limits(args.outdir)
        summary['limit_law_audit']={k:v for k,v in limit_summary.items()
                                  if k not in ('exact_moment_samples','laplace_checks','critical_r3_checks')}
        summary['limit_law_audit']['detail_file']='limit_law_audit.json'
        (Path(args.outdir)/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='sample_rows'},indent=2))
