#!/usr/bin/env python3
"""Independent exact Cauchy-minor and inventory checks. Standard library."""
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt
import json

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def v2(n):
    require(n != 0, "valuation of zero")
    n = abs(n)
    return (n & -n).bit_length() - 1

def weight(j, delta):
    return delta + 4*j - 2*j.bit_count()

def det(matrix):
    a = [list(map(F, row)) for row in matrix]
    n = len(a)
    ans = F(1)
    for k in range(n):
        pivot = next((i for i in range(k,n) if a[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            ans = -ans
        p = a[k][k]
        ans *= p
        for i in range(k+1,n):
            q = a[i][k]/p
            for j in range(k+1,n):
                a[i][j] -= q*a[k][j]
    return ans

def valuation_det(rows, cols, delta):
    k=len(rows)
    return (k*delta + k*(k-1)
            + sum(v2(rows[j]-rows[i]) for i in range(k) for j in range(i+1,k))
            + sum(v2(cols[j]-cols[i]) for i in range(k) for j in range(i+1,k)))

def main():
    minors = 0
    exact_dets = 0
    for J in range(1,8):
        for k in range(1,J+1):
            best = None
            for rows in combinations(range(J),k):
                for cols in combinations(range(J),k):
                    val=valuation_det(rows,cols,3)
                    best=val if best is None else min(best,val)
                    minors += 1
                    if J <= 4:
                        a=[[F(8,3+2*(r-c)) for c in cols] for r in rows]
                        d=det(a)
                        require(d != 0, "Cauchy minor vanished")
                        require(v2(d.numerator)-v2(d.denominator)==val,
                                "determinant valuation formula")
                        exact_dets += 1
            require(best==sum(weight(j,3) for j in range(k)),
                    "Smith determinantal-ideal profile")
    inventories = 0
    tuple_cases = 0
    for root_u in range(1,17):
        u=root_u**2
        for multiplier in [16,24,32,64]:
            D=multiplier*root_u
            for A in [1,2,5,13]:
                for delta in [1,multiplier//2,multiplier]:
                    q=D//(8*root_u)
                    P=(A*D*D+4*u-1)//(4*u)
                    total=A*sum(weight(j,delta) for j in range(q))
                    require(D>=16*root_u and delta<=D//root_u,"premises")
                    require(q*16*root_u>=D,"floor bound")
                    require(total<P,"binary inventory not below precision")
                    require(A*q<=A*D,"ordinary-degree bound")
                    require(F(A*(q*delta+2*q*(q-1)))<=F(5*A*D*D,32*u),
                            "symbolic upper estimate")
                    inventories += 1
    for A,q,delta,P in [(1,2,1,64),(2,3,2,256),(2,4,3,512)]:
        weights=sorted(weight(j,delta) for _ in range(A) for j in range(q))
        counts={}
        for beta in product([0,1], repeat=A*q):
            W=sum(a*b for a,b in zip(weights,beta))
            require(W<P,"enumerated tuple exceeds budget")
            counts[W]=counts.get(W,0)+1
            tuple_cases+=1
        require(max(counts.values())*P >= 2**(A*q),"pigeonhole exact-weight list")
    print(json.dumps({
        "status":"passed",
        "all_minor_valuation_cases":minors,
        "direct_fraction_determinants":exact_dets,
        "inventory_parameter_cases":inventories,
        "explicit_binary_tuples":tuple_cases,
        "scope":"finite checks of Cauchy profile and stated inventory inequalities; no SAT lower bound"
    },indent=2))

if __name__=="__main__":
    main()
