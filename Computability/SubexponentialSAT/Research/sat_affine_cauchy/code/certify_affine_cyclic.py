#!/usr/bin/env python3
"""Exact finite certificates for a new affine/cyclic cached contraction menu.

Standard-library only. This is not an implementation of the imported SAT
reduction, 2-adic contraction engine, or fast matrix multiplication backend.
Every explicit validation uses exceptions and remains active under python -O.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import json
from pathlib import Path


def require(ok,message):
    if not ok: raise RuntimeError(message)


def plans9():
    return [[[x for x in range(9) if (a*(x%3)+b*(x//3))%3==c]
             for c in range(3)] for a,b in ((1,0),(0,1),(1,1),(1,2))]


def plans13():
    seed=((11,2,8,9,7),(10,1,0,5),(6,4,3,12))
    return [[[ (x+d)%13 for x in block] for block in seed] for d in range(13)]


def supports(r,blocks):
    require(sorted(x for b in blocks for x in b)==list(range(r)),"Invalid partition")
    universe=set(range(r));tripartitions=[]
    def descend(xs):
        if len(xs)==1:return
        h=len(xs)//2;A=xs[:h];B=xs[h:]
        descend(A);descend(B)
        tripartitions.append((set(A),set(B),universe-set(xs)))
    for block in blocks: descend(block)
    tripartitions.append(tuple(set(b) for b in blocks))
    require(len(tripartitions)==r-2,"Operation count")
    edges=list(combinations(range(r),2)); rows=[]
    for parts in tripartitions:
        require(all(parts) and set.union(*parts)==universe,"Invalid tripartition")
        for discount in ((0,1),(0,2),(1,2)):
            row=[]
            for a,b in edges:
                i=next(i for i,p in enumerate(parts) if a in p)
                j=next(i for i,p in enumerate(parts) if b in p)
                row.append(0 if i==j else 2 if tuple(sorted((i,j)))==discount else 5)
            rows.append(tuple(row))
    return rows


def dot(u,v):return sum(a*b for a,b in zip(u,v))


def certify(r,plans):
    menus=[supports(r,p) for p in plans]
    q=len(plans);D=[]
    for first in menus:
        D.append([max(dot(u,v) for u in first for v in second) for second in menus])
    S=sum(map(sum,D));bsq=F(2*S,25*q*q*r*r)
    return {"groups":r,"plan_count":q,"supports_per_plan":list(map(len,menus)),
            "all_pairs_max_dot":D,"total":S,"b_squared":str(bsq)}


# Positive rational interval arithmetic for the numerical constants.
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0],a[1]*b[1])
def div(a,b):return (a[0]/b[1],a[1]/b[0])
def exact(x):x=F(x);return (x,x)
def root(x,digits=45):
    x=F(x);Q=10**digits;k=isqrt(x.numerator*Q*Q//x.denominator)
    return F(k,Q),F(k+1,Q)
def atan(x,N):
    x=F(x);s=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(N)),F(0))
    term=x**(2*N+1)/F(2*N+1)
    return (s,s+term) if N%2==0 else (s-term,s)
def pi_bounds():
    a=atan(F(1,5),40);b=atan(F(1,239),12)
    return 16*a[0]-4*b[1],16*a[1]-4*b[0]
def ln2_bounds():
    x=F(1,3);N=60;s=2*sum((x**(2*k+1)/F(2*k+1) for k in range(N)),F(0))
    err=2*x**(2*N+1)/(F(2*N+1)*(1-x*x))
    return s,s+err

def interval_decimal(x,places=15):
    Q=10**places
    lo=x[0].numerator*Q//x[0].denominator
    hi=-((-x[1].numerator*Q)//x[1].denominator)
    def string(n):return f'{n//Q}.{n%Q:0{places}d}'
    return [string(lo),string(hi)]


def constants():
    kap=mul(div(pi_bounds(),ln2_bounds()),root(2))
    K0=mul(kap,root(F(4000,63)))
    K1=mul(mul(kap,exact(F(2,9))),root(F(800,9)))
    K2=mul(mul(kap,exact(F(4,117))),root(F(16200,77)))
    lead=mul(exact(F(4,9)),K0)
    C0=div(K0,root(3))
    C1=add(lead,mul(root(F(56,169)),K1))
    Cinf=add(add(lead,mul(root(F(24,169)),K1)),mul(root(F(3,4)),K2))
    require(C1[1]<Cinf[0],"Depth-one branch is not below full path")
    require(C0[1]<Cinf[0],"Root branch is not below full path")
    require(Cinf[1]<F(30513,1000),"Time coefficient threshold failed")
    require(C0[1]<F(29488,1000),"Space coefficient threshold failed")
    require(mul(root(F(56,169)),K1)[1]<C0[0],"Depth-one local storage dominates")
    require(mul(root(F(632,1225)),K2)[1]<C0[0],"Tail storage dominates")
    return {"C0_root_and_space":interval_decimal(C0),"C1_depth_one":interval_decimal(C1),
            "Cinf_time":interval_decimal(Cinf),"eventual_time":30.513,"eventual_space":29.488}


def schedule():
    require(F(63,4000)+F(9,800)==F(27,1000),"Prefix capacity")
    require(F(27,1000)+F(77,16200)/(1-F(4,9))==F(8,225),"Total capacity")
    require(9**100<2**317 and 13**1000<2**3701 and 7**100<2**281,"Logarithm certificate")
    gaps=[1-F(9,10)-2*F(63,4000)*F(317,100),
          1-F(9,10)-F(27,1000)*F(3701,1000),
          1-F(9,10)-F(8,225)*F(281,100)]
    require(all(g>0 for g in gaps),"Packing slack")
    require(F(8,225)*(2*F(3701,1000)+1)<1,"Fresh side and rounding")
    require(F(9,4)**3<3**4,"Uniform taper divergence at hypothetical depth")
    require(F(632,1225)<F(3,4),"Tail aggregation versus full-path branch")
    return {"root_eta":"63/4000","depth_one_eta":"9/800","tail_eta":"77/16200",
            "tail_ratio":"4/9","tail_K_ratio":"3/7","strict_packing_gaps":[str(g) for g in gaps]}


def main():
    nine=certify(9,plans9()); thirteen=certify(13,plans13())
    require(nine['total']==5400 and nine['b_squared']=='1/3',"Affine certificate")
    require(nine['all_pairs_max_dot']==[[486 if i==j else 288 for j in range(4)] for i in range(4)],"Affine correlations")
    pattern=[1064,647,651,713,647,709,651,651,709,647,713,651,647]
    require(thirteen['all_pairs_max_dot']==[[pattern[(j-i)%13] for j in range(13)] for i in range(13)],"Cyclic correlations")
    require(thirteen['total']==118300 and thirteen['b_squared']=='56/169',"Cyclic certificate")
    result={"status":"PASS","scope":"Exact finite support and rational constant checks; inherited algorithm interfaces are assumptions", 
            "certificates":[nine,thirteen],"schedule":schedule(),"constants":constants()}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
