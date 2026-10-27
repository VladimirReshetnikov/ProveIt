#!/usr/bin/env python3
"""Independent integer check of the six-point partial affine doubling.

All geometry and supports are reconstructed in this file. Standard library
only; no imported optimizer. Checks remain enabled under python -O.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
from math import isqrt, pi, log, sqrt
import json


def require(x,reason):
    if not x: raise ValueError(reason)


R=15
L=1400000
V=tuple(range(R))
E=tuple(combinations(V,2))
NORMALS=((1,0),(0,1),(1,1),(1,2))
PAIR_CLASSES=((0,1),(0,2),(1,2))
TRIPLES=tuple(sorted(set(permutations((1400007,1400007,0)))))+tuple(
    sorted(set(permutations((1400000,1175014,750000)))))


def plans():
    result=[]
    for a,b in NORMALS:
        blocks=[]
        for c in range(3):
            old=tuple(3*x+y for x in range(3) for y in range(3) if (a*x+b*y)%3==c)
            blocks.append(old+tuple(p+9 for p in old if p<6))
        result.append(tuple(blocks))
    return tuple(result)


def make_supports(plan):
    operations=[]
    subsets=[]
    def build(block):
        subsets.append(block)
        if len(block)>1:
            k=len(block)//2
            a,b=block[:k],block[k:]
            build(a);build(b)
            operations.append((a,b,tuple(x for x in V if x not in block)))
    for block in plan: build(block)
    operations.append(plan)
    time=[]
    for parts in operations:
        label={x:i for i,p in enumerate(parts) for x in p}
        require(set(label)==set(V),"Bad operation partition")
        for triple in TRIPLES:
            mask=[]
            for a,b in E:
                if label[a]==label[b]:mask.append(0)
                else:mask.append(triple[PAIR_CLASSES.index(tuple(sorted((label[a],label[b]))))])
            time.append(tuple(mask))
    boundary=tuple(tuple(int((a in S)!=(b in S)) for a,b in E) for S in subsets)
    require(len(time)==117 and len(boundary)==27,"Wrong support count")
    return tuple(time),boundary


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def select_joint(cardinality_products):
    """Choose a joint plan by exact integers after per-edge upward rounding."""
    require(len(cardinality_products)==len(E),"Wrong cardinality vector length")
    require(all(isinstance(d,int) and d>=1 for d in cardinality_products),
            "Mode-list products must be positive integers")
    upper=tuple((d-1).bit_length() for d in cardinality_products)
    scores=[]
    for plan in plans():
        time,boundary=make_supports(plan)
        T=max(dot(v,upper) for v in time)
        B=max(dot(v,upper) for v in boundary)
        scores.append({"time_numerator_upper":T,"boundary_exponent_upper":B,
                       "score":max(T*T,2263800000000*B*B)})
    selected=min(range(4),key=lambda j:scores[j]["score"])
    return {"selected_plan":selected,"plans":scores,"upper_entropies":upper}


def audit_schedule(beta2,sigma2):
    """Exact paid-time and sharper-memory comparison for 15 -> 10 -> 7 -> 4."""
    f=Fraction
    groups=(15,10,7,4)
    eta=(f(567,5000),f(87,5000),f(407,20000),f(1443,80000))
    tail_q=f(63,100)
    bs=(beta2,f(15952347164548384057,49000000000000000000),f(891,2450),f(13,25))
    mass=(f(1),f(2,15),f(2,75),f(4,525))
    require(sum(eta[:3])+eta[3]/(1-tail_q)==f(1999,10000),"Capacity sum fails")
    for base,power,target in ((450,567,5000),(200,327,2500),(98,3023,20000)):
        require(base**power<2**target,"A prefix capacity fails")
    require(5*f(1999,10000)<1,"Tail capacity fails")
    require(eta[0]>f(1,12),"Initial degree history fails")
    require(tail_q>f(11,20)>f(1,2),"Growing tail tapers for H=s/lambda fail")
    def rt(x):
        scale=10**40
        a=isqrt(x.numerator*scale*scale//x.denominator)
        return f(a,scale),f(a+1,scale)
    def add(a,b):return a[0]+b[0],a[1]+b[1]
    def mul(a,b):return a[0]*b[0],a[1]*b[1]
    prefix=(f(0),f(0)); paid=[]
    for d,r in enumerate(groups):
        K=rt(mass[d]**2/eta[d])
        alpha=rt(f(2*(r-1),r*r))
        if d<3:
            paid.append(add(prefix,mul(rt(bs[d]),K)))
        else:
            gamma=rt(f(25,63))
            tail=(alpha[0]/(1-gamma[0]),alpha[1]/(1-gamma[1]))
            require(tail[0]>rt(bs[d])[1],"Need both tail endpoints")
            paid.append(add(prefix,mul(tail,K)))
        prefix=add(prefix,mul(alpha,K))
    require(all(paid[0][0]>cost[1] for cost in paid[1:]),"Root time does not dominate")
    space_radicands=[2*sigma2/eta[0]]+[2*bs[d]*mass[d]**2/eta[d] for d in range(1,4)]
    require(all(space_radicands[0]>v for v in space_radicands[1:]),
            "Sharper root space does not dominate tail")
    # Decimal values below illustrate proved comparisons; they are not inputs.
    return {"groups":groups,"etas":[str(x) for x in eta],"tail_ratio":str(tail_q),
            "leaf_threshold":"ceil(s/lambda)","total_capacity":"1999/10000",
            "root_time_strictly_dominates":True,"root_joint_space_strictly_dominates":True,
            "paid_time_coefficients_approx":[pi*sqrt(2)/log(2)*float((x[0]+x[1])/2) for x in paid],
            "local_space_radicands_after_pi_over_ln2":[str(x) for x in space_radicands],
            "local_space_coefficients_approx":[pi/log(2)*sqrt(float(x)) for x in space_radicands]}


def audit():
    menus=tuple(make_supports(p) for p in plans())
    nt=tuple(tuple(dot(t,t) for t in m[0]) for m in menus)
    nb=tuple(tuple(dot(b,b) for b in m[1]) for m in menus)
    pairs=[]
    tt_count=bb_count=0
    for i,j in combinations(range(4),2):
        A=0;B=0
        for a,t in enumerate(menus[i][0]):
            for b,u in enumerate(menus[j][0]):
                A=max(A,nt[i][a]+nt[j][b]+6*dot(t,u));tt_count+=1
        for a,t in enumerate(menus[i][1]):
            for b,u in enumerate(menus[j][1]):
                B=max(B,nb[i][a]+nb[j][b]+6*dot(t,u));bb_count+=1
        pairs.append({"i":i,"j":j,"time_pair":A,"boundary_pair":B})
    require([p["time_pair"] for p in pairs]==[580173494513132]*3+[572279799215680]*3,
            "Time pair certificate mismatch")
    # A pure-boundary limiting scale is too large for some mixed pairs.
    # Use the displayed rational scale, then certify every mixed pair exactly.
    x_squared=Fraction(231*L**2,200)
    require(all(x_squared*p["boundary_pair"]<=p["time_pair"] for p in pairs),
            "Scaled boundary pair exceeds its time allowance")
    numer,denom=x_squared.numerator,x_squared.denominator
    mixed_count=0
    min_D=min_gap=None
    for pair in pairs:
        i,j,A=pair["i"],pair["j"],pair["time_pair"]
        for ti,bi in ((i,j),(j,i)):
            for k,t in enumerate(menus[ti][0]):
                for m,b in enumerate(menus[bi][1]):
                    inner=dot(t,b)
                    D=(A-nt[ti][k])*denom-numer*nb[bi][m]
                    gap=D*D-36*numer*denom*inner*inner
                    require(D>=0 and gap>=0,"Mixed pair violates joint allowance")
                    min_D=D if min_D is None else min(min_D,D)
                    min_gap=gap if min_gap is None else min(min_gap,gap)
                    mixed_count+=1
    sum_A=sum(p["time_pair"] for p in pairs)
    beta2=Fraction(sum_A,24*L**2*R**2)
    rho2=x_squared/L**2
    sigma2=beta2/rho2
    eta0=Fraction(567,5000)
    schedule=audit_schedule(beta2,sigma2)
    selector_checks=[]
    for dims in ([1]*len(E),[2**(i%7) for i in range(len(E))],
                 [2**(i%7)+1 for i in range(len(E))]):
        selected=select_joint(dims)
        require(selected["plans"][selected["selected_plan"]]["score"]
                ==min(p["score"] for p in selected["plans"]),"Selector failed")
        for d,h in zip(dims,selected["upper_entropies"]):
            require(d<=2**h and (h==0 or 2**(h-1)<d),"Wrong upward entropy")
        selector_checks.append({"selected_plan":selected["selected_plan"],
                                "score":selected["plans"][selected["selected_plan"]]["score"]})
    return {"status":"PASS","plans":plans(),"time_supports_per_plan":117,
            "boundary_supports_per_plan":27,"pairs":pairs,
            "time_pairs_checked":tt_count,"boundary_pairs_checked":bb_count,
            "mixed_pairs_checked":mixed_count,"min_mixed_D":min_D,
            "min_mixed_squared_gap":min_gap,
            "beta_squared":str(beta2),"rho_squared":str(rho2),
            "sigma_squared":str(sigma2),"root_eta":str(eta0),
            "root_time_radicand_after_pi_over_ln2":str(2*beta2/eta0),
            "root_space_radicand_after_pi_over_ln2":str(2*sigma2/eta0),
            "selector_x_squared":str(x_squared),
            "selector_score":"max(T_hat_j^2, 2263800000000*B_hat_j^2)",
            "selector_upper_entropies":"g_hat_e=(D_e-1).bit_length()",
            "selector_checks":selector_checks,
            "schedule":schedule,
            "scope":"Exact local joint-support certificate and complete paid schedule comparison, relative to the stated inherited interfaces and tail certificates."}


if __name__=="__main__":
    result=audit()
    text=json.dumps(result,indent=2,sort_keys=True)+"\n"
    (Path(__file__).resolve().parents[1] / "results" / "partial_affine_joint_result.json").write_text(text)
    print(text,end="")
