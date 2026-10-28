#!/usr/bin/env python3
"""Exact orbit counts and coefficient interval for adaptive r=16 separators."""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import json

from verify_schedule import (atan_inverse_interval, log_ratio_interval,
                             sqrt_decimal_interval, check)


def balanced_paths(vertices, inherited=frozenset()):
    if len(vertices)==1:
        return [(vertices[0],inherited)]
    a,b=vertices[:len(vertices)//2],vertices[len(vertices)//2:]
    cut=frozenset(tuple(sorted((x,y))) for x in a for y in b)
    return balanced_paths(a,inherited|cut)+balanced_paths(b,inherited|cut)


def orbit_certificate():
    r=16
    edges=list(combinations(range(r),2))
    paths=balanced_paths(tuple(range(r)))
    check(len(paths)==16,"wrong leaf count")
    check(all(len(s)==85 for _,s in paths),"wrong path cardinality")
    indicators={e:tuple(int(e in s) for _,s in paths) for e in edges}
    totals={k:Q(0) for k in ("equal","adjacent","disjoint")}
    counts={k:0 for k in totals}
    for j,e in enumerate(edges):
        for f in edges[j:]:
            typ=("equal" if e==f else
                 "adjacent" if set(e)&set(f) else "disjoint")
            x,y=indicators[e],indicators[f]
            cov=Q(sum(a*b for a,b in zip(x,y)),r)-Q(sum(x)*sum(y),r*r)
            totals[typ]+=cov
            counts[typ]+=1
    coef={k:totals[k]/counts[k] for k in totals}
    expected={"equal":Q(19,192),"adjacent":Q(5,168),
              "disjoint":-Q(179,17472)}
    check(coef==expected,"orbit covariance coefficients differ")
    check(counts=={"equal":120,"adjacent":1680,"disjoint":5460},
          "orbit sizes differ")
    d,a,b=(coef[k] for k in ("equal","adjacent","disjoint"))
    eigen_constant=d+28*a+91*b
    eigen_vertex=d-b+12*(a-b)
    eigen_remaining=d-b-2*(a-b)
    check(eigen_constant==0,"constant covariance eigenvalue is not zero")
    check(eigen_vertex==Q(33,56),"vertex eigenvalue differs")
    check(eigen_remaining==Q(85,2912),"remaining eigenvalue differs")
    check(0<=eigen_remaining<=eigen_vertex,"PSD/top-eigenvalue certificate failed")
    beta2=(Q(120)*Q(17,24)**2+15*eigen_vertex)/128
    check(beta2==Q(725,1344),"incorrect adaptive coefficient")
    check(beta2/Q(170,256)==Q(290,357),"incorrect predecessor ratio")
    return {"groups":r,"leaves":len(paths),"unordered_pairs":len(edges),
            "unordered_pairs_per_path":85,"orbit_counts":counts,
            "covariance_entries":{k:str(v) for k,v in coef.items()},
            "eigenvalues":[str(eigen_constant),str(eigen_vertex),str(eigen_remaining)],
            "adaptive_local_coefficient_squared":str(beta2),
            "squared_ratio_to_predecessor":"290/357"}


def coefficient_interval():
    a0,a1=atan_inverse_interval(5)
    b0,b1=atan_inverse_interval(239)
    pi0,pi1=16*a0-4*b1,16*a1-4*b0
    ln0,ln1=log_ratio_interval(Q(1,3))
    scale=10**80
    k=isqrt(3*scale*scale)
    sqrt3lo,sqrt3hi=Q(k,scale),Q(k+1,scale)
    check(sqrt3lo**2<3<sqrt3hi**2,"sqrt3 enclosure failed")
    f0,f1=1+1/(3*sqrt3hi),1+1/(3*sqrt3lo)
    c0=Q(3625,42)*pi0*pi0*f0*f0/(ln1*ln1)
    c1=Q(3625,42)*pi1*pi1*f1*f1/(ln0*ln0)
    check(Q(5021,100)**2<c0<c1<Q(2511,50)**2,
          "coefficient interval not inside (50.21,50.22)")
    return {"coefficient_interval":sqrt_decimal_interval(c0,c1),
            "safe_eventual_coefficient":"50.22","space":"polynomial",
            "constant_formula":"5*pi/ln(2)*sqrt(145/42)*(1+1/(3*sqrt(3)))"}


def main():
    result={"finite_combinatorial_certificate":orbit_certificate(),
            "asymptotic_coefficient":coefficient_interval(),
            "scope":"exact finite identities plus rational coefficient bounds; not a SAT benchmark"}
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
