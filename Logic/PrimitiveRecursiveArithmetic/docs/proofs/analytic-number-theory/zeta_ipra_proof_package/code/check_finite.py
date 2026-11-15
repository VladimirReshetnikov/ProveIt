#!/usr/bin/env python3
"""Exact finite checks; these are regression evidence, not universal proofs."""
from fractions import Fraction as Q
from math import comb, factorial
import json
from pathlib import Path
from zeta_certificates import (CQ, Ball, bernoullis, bernoulli_coefficients,
                               zeta_em, em_remainder, samples, dyadic)


def falling(n, k):
    if k > n:
        return 0
    return factorial(n)//factorial(n-k)


def poly_value(coeff, x):
    ans = Q(0)
    for c in reversed(coeff):
        ans = ans*x+c
    return ans


def em_monomial(n, upper, m, degree):
    left = sum((Q(j)**degree for j in range(n,upper)), Q(0))
    right = Q(upper**(degree+1)-n**(degree+1),degree+1)
    right += Q(n**degree-upper**degree,2)
    b = bernoullis(2*m)
    for k in range(1,m+1):
        order = 2*k-1
        if order <= degree:
            right += (b[2*k]/factorial(2*k)*falling(degree,order)
                      *(upper**(degree-order)-n**(degree-order)))
    integral = Q(0)
    if 2*m <= degree:
        coeff = bernoulli_coefficients(2*m)
        d = degree-2*m
        for cell in range(n,upper):
            for i,c in enumerate(coeff):
                for j in range(d+1):
                    integral += c*comb(d,j)*cell**(d-j)/Q(i+j+1)
        integral *= falling(degree,2*m)
    right -= integral/factorial(2*m)
    assert left == right, (n,upper,m,degree,left,right)
    return integral != 0


def main():
    counts = {}
    b=bernoullis(24)
    known={0:Q(1),1:Q(-1,2),2:Q(1,6),4:Q(-1,30),6:Q(1,42),
           8:Q(-1,30),10:Q(5,66),12:Q(-691,2730)}
    for k,v in known.items():
        assert b[k] == v
    counts['known_bernoulli_values'] = len(known)
    checks=0
    for n in range(1,25):
        c=bernoulli_coefficients(n)
        prev=bernoulli_coefficients(n-1)
        assert tuple((j+1)*c[j+1] for j in range(n)) == tuple(n*x for x in prev)
        assert sum((c[j]/Q(j+1) for j in range(n+1)),Q(0)) == 0
        checks +=2
        if n>=2:
            assert poly_value(c,1)==c[0]
            checks+=1
        for x in [Q(0),Q(1,7),Q(1,2),Q(6,7),Q(1),Q(5,3)]:
            assert poly_value(c,1-x)==(-1)**n*poly_value(c,x)
            assert poly_value(c,x+1)-poly_value(c,x)==n*x**(n-1)
            checks+=2
    counts['bernoulli_polynomial_identities']=checks
    total=nonzero=0
    for m in range(1,6):
        for degree in range(13):
            for n in range(1,4):
                for gap in range(1,5):
                    nonzero+=em_monomial(n,n+gap,m,degree)
                    total+=1
    counts['exact_euler_maclaurin_identities']=total
    counts['with_nonzero_integral_remainder']=nonzero
    for q in range(13):
        value = Q(-1,2) if q==0 else -b[q+1]/Q(q+1)
        ans=zeta_em(CQ(-q),n=7,m=q+2,bits=60)
        assert ans.r == 0 and ans.c == CQ(value)
    counts['exact_nonpositive_integer_values']=13
    # Exact test points inside each ball, and their products after rounding.
    checks=0
    for a in [CQ(Q(1,3),Q(2,7)), CQ(-2,1), CQ(0)]:
        for b0 in [CQ(Q(3,5),-1),CQ(2),CQ(-1,2)]:
            for da in [CQ(Q(1,16)),CQ(0,Q(-1,16)),CQ(Q(1,32),Q(1,32))]:
                for db in [CQ(Q(-1,32)),CQ(0,Q(1,32))]:
                    x=Ball(a,Q(1,8)); y=Ball(b0,Q(1,8))
                    product=(x*y).rounded(40)
                    exact=(a+da)*(b0+db)
                    assert (product.c-exact).norm1()<=product.r
                    checks+=1
    counts['ball_product_containment_instances']=checks
    # Different truncations must have intersecting enclosures.
    checks=0
    for s in [CQ(Q(1,2)),CQ(Q(3,2),2),CQ(-2,3),CQ(2)]:
        a=zeta_em(s,24,9,70); c=zeta_em(s,32,10,70)
        assert (a.c-c.c).norm1()<=a.r+c.r
        checks+=1
    counts['independent_truncation_overlap_checks']=checks
    result=samples()
    assert all(row['radius_lt_2_pow_minus_30'] for row in result.values())
    root=Path(__file__).resolve().parents[1]
    (root/'verification'/'enclosures.json').write_text(json.dumps(result,indent=2)+'\n')
    report={'status':'PASS','arithmetic':'exact fractions.Fraction only',
            'counts':counts,
            'limitation':'Finite instance checks, not a universal or formal iPRA proof.'}
    (root/'verification'/'finite_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
