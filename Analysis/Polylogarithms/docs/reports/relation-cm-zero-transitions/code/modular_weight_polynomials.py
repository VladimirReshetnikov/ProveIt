#!/usr/bin/env python3
"""Generate and certify Ew^12/Delta^w = Fw(j) over Q for even weights.

The normalized Eisenstein series is
    Ew = 1 - (2w/Bw) * sum_{m>=1} sigma_{w-1}(m) q^m.
Delta is generated independently from q*product_{m>=1}(1-q^m)^24.
Every identity is checked at all coefficients q^0,...,q^w; both sides
after clearing Delta^w are holomorphic modular forms of weight 12w,
so the level-one Sturm bound certifies the identity.

Only Python's standard library is required.  All arithmetic is exact.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def bernoulli(n):
    values=[Q(1)]
    for m in range(1,n+1):
        values.append(-sum(Q(comb(m+1,k))*values[k]
                           for k in range(m))/Q(m+1))
    return values[n]


def add(a,b,N):
    return [(a[j] if j<len(a) else Q(0))
            +(b[j] if j<len(b) else Q(0)) for j in range(N+1)]


def scale(a,c):
    return [c*v for v in a]


def mul(a,b,N):
    result=[Q(0)]*(N+1)
    for j,aj in enumerate(a[:N+1]):
        if aj:
            for k,bk in enumerate(b[:N-j+1]):
                if bk:
                    result[j+k] += aj*bk
    return result


def power(a,e,N):
    assert e>=0
    result=[Q(1)]+[Q(0)]*N
    while e:
        if e&1:
            result=mul(result,a,N)
        e//=2
        if e:
            a=mul(a,a,N)
    return result


def eisenstein(w,N):
    assert w>=4 and w%2==0
    sigmas=[0]*(N+1)
    for d in range(1,N+1):
        term=d**(w-1)
        for m in range(d,N+1,d):
            sigmas[m]+=term
    factor=-Q(2*w)/bernoulli(w)
    return [Q(1)]+[factor*sigmas[m] for m in range(1,N+1)]


def delta_product(N):
    product=[Q(1)]+[Q(0)]*(N-1)
    for m in range(1,N):
        factor=[Q(0)]*N
        for r in range(min(24,(N-1)//m)+1):
            factor[m*r]=Q((-1)**r*comb(24,r))
        product=mul(product,factor,N-1)
    return [Q(0)]+product


def monomial_polynomial(degree):
    return [Q(0)]*degree+[Q(1)]


def trim(poly):
    while len(poly)>1 and not poly[-1]:
        poly.pop()
    return poly


def polymul(a,b):
    return trim(mul(a,b,len(a)+len(b)-2))


def polypower(a,e):
    result=[Q(1)]
    while e:
        if e&1:
            result=polymul(result,a)
        e//=2
        if e:
            a=polymul(a,a)
    return result


def strq(q):
    return str(q.numerator) if q.denominator==1 else f"{q.numerator}/{q.denominator}"


def polynomial_text(coefficients,variable="X"):
    terms=[]
    for j,c in reversed(list(enumerate(coefficients))):
        if not c:
            continue
        magnitude=abs(c)
        if j==0:
            term=strq(magnitude)
        else:
            atom=variable if j==1 else f"{variable}^{j}"
            term=atom if magnitude==1 else f"({strq(magnitude)})*{atom}"
        if not terms:
            terms.append(("-" if c<0 else "")+term)
        else:
            terms.append((" - " if c<0 else " + ")+term)
    return "".join(terms) or "0"


def residue_exponents(w):
    choices=[(a,b,(w-4*a-6*b)//12)
             for a in range(3) for b in range(2)
             if w>=4*a+6*b and (w-4*a-6*b)%12==0]
    assert len(choices)==1
    return choices[0]


def generate(w):
    N=w
    E4=eisenstein(4,N)
    E6=eisenstein(6,N)
    Ew=eisenstein(w,N)
    Delta=delta_product(N)
    assert add(add(power(E4,3,N),scale(power(E6,2,N),Q(-1)),N),
               scale(Delta,Q(-1728)),N)==[Q(0)]*(N+1)
    a,b,c=residue_exponents(w)

    # Unit triangular q-basis: basis[j] has leading q^(c-j), coefficient 1.
    basis=[mul(mul(power(E4,a+3*j,N),power(E6,b,N),N),
               power(Delta,c-j,N),N) for j in range(c+1)]
    residual=Ew[:]
    P=[Q(0)]*(c+1)
    for r in range(c+1):
        j=c-r
        assert basis[j][r]==1 and all(not x for x in basis[j][:r])
        P[j]=residual[r]
        residual=add(residual,scale(basis[j],-P[j]),N)
    assert P[-1]==1
    sturm_small=w//12
    assert all(not residual[j] for j in range(sturm_small+1))
    # More coefficients are available; retain them as a stronger finite replay.
    assert all(not x for x in residual)

    F=polymul(polymul(monomial_polynomial(4*a),
                     polypower([Q(-1728),Q(1)],6*b)),polypower(P,12))
    assert len(F)==w+1 and F[-1]==1

    # Independent direct cleared-denominator Sturm check in weight 12w.
    lhs=power(Ew,12,N)
    rhs=[Q(0)]*(N+1)
    for j,fj in enumerate(F):
        if fj:
            term=mul(power(E4,3*j,N),power(Delta,w-j,N),N)
            rhs=add(rhs,scale(term,fj),N)
    assert lhs==rhs

    factors=[]
    if a:
        factors.append(f"X^{4*a}")
    if b:
        factors.append(f"(X-1728)^{6*b}")
    if c:
        factors.append(f"({polynomial_text(P)})^12")
    factorized=" * ".join(factors) or "1"

    return {
        "weight":w,
        "Bernoulli_number":strq(bernoulli(w)),
        "Ew_first_q_coefficient":strq(Ew[1]),
        "a":a,"b":b,"c":c,
        "reduced_polynomial_P_coefficients_ascending":[strq(x) for x in P],
        "reduced_polynomial_P":polynomial_text(P),
        "F_coefficients_ascending":[strq(x) for x in F],
        "F_factorized":factorized,
        "F_degree":len(F)-1,"F_monic":F[-1]==1,
        "ring_identity":"Ew = E4^a * E6^b * Delta^c * P(j)",
        "small_weight_certificate":{
            "modular_weight":w,"level":1,"Sturm_bound":sturm_small,
            "coefficients_checked_inclusive":[0,w],
            "all_exact_residuals_zero":True},
        "cleared_identity_certificate":{
            "identity":"Ew^12 = sum_j F[j] * E4^(3j) * Delta^(w-j)",
            "modular_weight":12*w,"level":1,"Sturm_bound":w,
            "coefficients_checked_inclusive":[0,w],
            "left_coefficients":[strq(x) for x in lhs],
            "all_exact_residuals_zero":True,
            "residual_numerators":[0]*(w+1)},
        "normalization_check":"E4^3 - E6^2 - 1728*Delta has exact zero coefficients q^0 through q^w; Delta generated by Euler product.",
    }


def main(max_weight,output):
    assert max_weight>=4 and max_weight%2==0
    results=[]
    for w in range(4,max_weight+1,2):
        result=generate(w)
        results.append(result)
        print(json.dumps({"weight":w,"F":result["F_factorized"],
                          "Sturm_bound":w,"certified":True}),flush=True)
    known={
        4:"X^4",6:"(X-1728)^6",8:"X^8",10:"X^4 * (X-1728)^6",
        12:"(X - 432000/691)^12",14:"X^8 * (X-1728)^6",
        16:"X^4 * (X - 3456000/3617)^12",
    }
    for result in results:
        if result["weight"] in known:
            assert result["F_factorized"]==known[result["weight"]]
    package={
        "normalization":{
            "Ew":"1 - (2w/Bw) sum_(m>=1) sigma_(w-1)(m) q^m",
            "Delta":"q product_(m>=1)(1-q^m)^24 = (E4^3-E6^2)/1728",
            "j":"E4^3/Delta",
            "F_definition":"Ew^12/Delta^w = Fw(j)"},
        "coefficient_field":"Q",
        "coefficient_order":"ascending powers of X",
        "certification_theorem":"Level-one Sturm bound: a holomorphic modular form of weight k is zero if its coefficients q^0 through q^floor(k/12) vanish.",
        "construction":"Unit triangular q-expansion solve in E4^a E6^b sum_(j=0)^c p_j E4^(3j) Delta^(c-j), then F=X^(4a)(X-1728)^(6b) P^12.",
        "results":results,
    }
    output.write_text(json.dumps(package,indent=2)+"\n")


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--max-weight",type=int,default=24)
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).with_name("modular_weight_polynomials.json"))
    args=parser.parse_args()
    main(args.max_weight,args.output)
