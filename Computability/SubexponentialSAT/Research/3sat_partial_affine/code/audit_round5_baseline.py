#!/usr/bin/env python3
"""Exact round-5-compatible low-degree comparison certificate.

This independently recomposes existing cyclic13, weighted10, punctured8,
and fixed6 menus. It is a comparison bound, not a global optimum claim.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt, pi, log, sqrt
from audit_round5_new15 import pi_ln2, decimals
from pathlib import Path
import json

def require(condition,message):
    if not condition:raise RuntimeError(message)

DEN=1_400_000
TRIPLES=sorted(set(permutations((1_400_007,1_400_007,0))) |
               set(permutations((1_400_000,1_175_014,750_000))))

def cyclic_plan(d):
    return [[(v+d)%13 for v in block] for block in
            [[11,2,8,9,7],[10,1,0,5],[6,4,3,12]]]

def supports(plan):
    edges=list(combinations(range(13),2));universe=set(range(13));out=[]
    def operation(parts):
        labels={v:j for j,part in enumerate(parts) for v in part}
        class_of={(0,1):0,(0,2):1,(1,2):2}
        kinds=[None if labels[a]==labels[b] else
               class_of[tuple(sorted((labels[a],labels[b])))] for a,b in edges]
        for weights in TRIPLES:
            out.append(tuple(0 if kind is None else weights[kind] for kind in kinds))
    def visit(block):
        if len(block)<2:return
        cut=len(block)//2;a,b=block[:cut],block[cut:]
        visit(a);visit(b);operation((a,b,universe-set(block)))
    for block in plan:visit(block)
    operation(plan)
    require(len(out)==99,"Exact baseline audit check at original line 40 failed")
    return out

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def coupled_cyclic13():
    base=supports(cyclic_plan(0));norm0=[dot(v,v) for v in base]
    first_row=[]
    for d in range(1,13):
        shifted=supports(cyclic_plan(d));normd=[dot(v,v) for v in shifted]
        first_row.append(max(norm0[i]+normd[j]+24*dot(v,w)
                             for i,v in enumerate(base) for j,w in enumerate(shifted)))
    require(first_row==list(reversed(first_row)),"Exact baseline audit check at original line 52 failed")
    # Global cyclic relabeling preserves the ordered subtree construction.
    # Thus every pair row is this same circulant row; divide by two for i<j.
    pair_sum=13*sum(first_row)//2
    require(13*sum(first_row)%2==0,"Exact baseline audit check at original line 56 failed")
    b2=F(2*pair_sum,12*13**2*DEN**2*13**2)
    require(b2==F(511416908935241,1614795000000000),"Exact baseline audit check at original line 58 failed")
    return b2,first_row

def rt(x):
    x=F(x);scale=10**45
    j=isqrt(x.numerator*scale*scale//x.denominator)
    return F(j,scale),F(j+1,scale)
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def times(a,b):return a[0]*b[0],a[1]*b[1]
def div(a,b):
    require(b[0]>0,"Exact baseline audit check at original line 68 failed")
    return a[0]/b[1],a[1]/b[0]
def constant(x):return F(x),F(x)

def main():
    b13,first_row=coupled_cyclic13()
    beta2=[b13,F(15952347164548384057,49000000000000000000),
           F(279,800),F(12,25)]
    rs=[13,10,8,6]
    eta=[F(1007,10000),F(301,10000),F(3,250),F(156,15625)]
    q=F(12,25)
    require(sum(eta[:2])==F(327,2500),"Exact baseline audit check at original line 79 failed")
    require(sum(eta[:3])==F(357,2500),"Exact baseline audit check at original line 80 failed")
    require(sum(eta[:3])+eta[3]/(1-q)==F(81,500),"Exact baseline audit check at original line 81 failed")
    require(338**1007 < 2**10000,"Exact baseline audit check at original line 82 failed")
    require(200**327 < 2**2500,"Exact baseline audit check at original line 83 failed")
    require(7*F(357,2500)<1,"Exact baseline audit check at original line 84 failed")
    require(72**81 < 2**500,"Exact baseline audit check at original line 85 failed")
    require(F(1,12)<eta[0],"Exact baseline audit check at original line 86 failed")
    require(F(1,3)<F(2,5),"Exact baseline audit check at original line 87 failed")
    require(F(25,12)**2 < F(5,2)**3,"Exact baseline audit check at original line 88 failed")
    prefix=constant(0);mass=F(1);costs=[]
    for d,(r,e,b2) in enumerate(zip(rs,eta,beta2)):
        kd=rt(mass*mass/e)
        alpha=rt(F(2*(r-1),r*r))
        if d<3:
            costs.append(plus(prefix,times(rt(b2),kd)))
        else:
            gamma=div(constant(F(1,3)),rt(q))
            tail=div(alpha,(1-gamma[1],1-gamma[0]))
            require(tail[0]>rt(b2)[1],"Exact baseline audit check at original line 98 failed")
            costs.append(plus(prefix,times(tail,kd)))
        prefix=plus(prefix,times(alpha,kd));mass*=F(2,r)
    require(all(costs[0][0]>c[1] for c in costs[1:]),"Exact baseline audit check at original line 101 failed")
    factor=2*b13/eta[0]
    kappa=pi*sqrt(2)/log(2)
    result={
      "status":"passed",
      "cyclic13_coupled_first_row_off_diagonal":first_row,
      "cyclic13_beta_squared":str(b13),
      "schedule":{"groups":rs,"etas_prefix_and_tail_initial":list(map(str,eta)),
                  "tail_ratio":str(q),"total_capacity":"81/500"},
      "root_radical_factor":str(factor),
      "root_time_and_space_display":pi/log(2)*sqrt(float(factor)),
      "paid_branches_display":[kappa*float(c[0]) for c in costs],
      "scope":"A concrete recomposition of round-5 ingredients; global optimality is not claimed.",
      "imported_local_coefficients":"weighted beta10, punctured beta7, fixed beta6 and beta4 are imported from their source certificates"
    }
    # A stronger entirely prior-ingredient five-stage composition.
    rs2=[13,10,7,6,4]
    eta2=[F(2051,20000),F(113,4000),F(407,20000),F(217,20000),F(14023,1000000)]
    beta22=[b13,beta2[1],F(891,2450),F(12,25),F(13,25)]
    q2=F(63,100)
    require(sum(eta2[:2])==F(327,2500),"Exact baseline audit check at original line 120 failed")
    require(sum(eta2[:3])==F(3023,20000),"Exact baseline audit check at original line 121 failed")
    require(sum(eta2[:4])==F(81,500),"Exact baseline audit check at original line 122 failed")
    require(sum(eta2[:4])+eta2[4]/(1-q2)==F(1999,10000),"Exact baseline audit check at original line 123 failed")
    require(338**2051<2**20000,"Exact baseline audit check at original line 124 failed")
    require(200**327<2**2500,"Exact baseline audit check at original line 125 failed")
    require(98**3023<2**20000,"Exact baseline audit check at original line 126 failed")
    require(72**81<2**500,"Exact baseline audit check at original line 127 failed")
    require(5*F(1999,10000)<1,"Exact baseline audit check at original line 128 failed")
    require(F(1,12)<eta2[0],"Exact baseline audit check at original line 129 failed")
    require(F(1,2)<F(11,20),"Exact baseline audit check at original line 130 failed")
    require(F(100,63)<F(20,11),"Exact baseline audit check at original line 131 failed")
    prefix=constant(0);mass=F(1);costs2=[]
    for d,(r,e,b2) in enumerate(zip(rs2,eta2,beta22)):
        kd=rt(mass*mass/e);alpha=rt(F(2*(r-1),r*r))
        if d<4:costs2.append(plus(prefix,times(rt(b2),kd)))
        else:
            gamma=div(constant(F(1,2)),rt(q2))
            tail=div(alpha,(1-gamma[1],1-gamma[0]))
            require(tail[0]>rt(b2)[1],"Exact baseline audit check at original line 139 failed")
            costs2.append(plus(prefix,times(tail,kd)))
        prefix=plus(prefix,times(alpha,kd));mass*=F(2,r)
    require(all(costs2[0][0]>c[1] for c in costs2[1:]),"Exact baseline audit check at original line 142 failed")
    factor2=2*b13/eta2[0]
    pi_interval,ln2_interval=pi_ln2()
    kappa_interval=times(div(pi_interval,ln2_interval),rt(2))
    costs2_intervals=[times(kappa_interval,c) for c in costs2]
    require(costs2_intervals[0][1]<F(11265,1000),"Safe baseline coefficient 11.265 failed")
    result["stronger_five_stage"]={
      "groups":rs2,"etas_prefix_and_tail_initial":list(map(str,eta2)),
      "tail_ratio":str(q2),"total_capacity":"1999/10000",
      "root_radical_factor":str(factor2),
      "root_time_and_space_display":pi/log(2)*sqrt(float(factor2)),
      "time_and_space_enclosure":decimals(costs2_intervals[0]),
      "paid_branch_enclosures":[decimals(c) for c in costs2_intervals],
      "leaf_threshold":"ceil(s/ceil(log2(s)))",
      "paid_branches_display":[kappa*float(c[0]) for c in costs2]
    }
    (Path(__file__).resolve().parents[1] / "results" / "round5_baseline_audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
