#!/usr/bin/env python3
"""Independent exact Fraction jets for the fourth radial and second n-correction.

Sparse multivariate polynomials: the first exponent is the truncated series
variable; all remaining exponents are independent formal parameters. No SymPy
or floating-point computation is used. Finite jets check algebra, not analytic
remainder estimates or convergence.
"""
from fractions import Fraction as Q
from math import factorial
import json


def need(condition,message):
    if not condition: raise ValueError(message)


def term(powers,value=1):
    return {tuple(powers):Q(value)} if value else {}


def add(*polynomials):
    out={}
    for polynomial in polynomials:
        for powers,value in polynomial.items():
            out[powers]=out.get(powers,Q(0))+value
    return {powers:value for powers,value in out.items() if value}


def scale(polynomial,value):
    return {powers:coefficient*value for powers,coefficient in polynomial.items() if coefficient*value}


def multiply(left,right,order):
    out={}
    for a,x in left.items():
        for b,y in right.items():
            powers=tuple(i+j for i,j in zip(a,b))
            if powers[0]<=order:
                out[powers]=out.get(powers,Q(0))+x*y
    return {powers:value for powers,value in out.items() if value}


def shift(polynomial,offset):
    out={}
    for powers,value in polynomial.items():
        shifted=tuple(a+b for a,b in zip(powers,offset))
        need(all(exponent>=0 for exponent in shifted),'negative formal exponent')
        out[shifted]=value
    return out


def power(polynomial,k,order,variables):
    out=term((0,)*variables)
    for _ in range(k):out=multiply(out,polynomial,order)
    return out


def exponential(polynomial,order,variables):
    need(all(powers[0]>0 for powers in polynomial),'exp jet needs zero constant term')
    return add(*(scale(power(polynomial,k,order,variables),Q(1,factorial(k))) for k in range(order+1)))


def logarithm(one_plus,order,variables):
    p=add(one_plus,term((0,)*variables,-1))
    need(all(powers[0]>0 for powers in p),'log jet needs constant one')
    return add(*(scale(power(p,k,order,variables),Q((-1)**(k+1),k)) for k in range(1,order+1)))


def binomial(p,alpha,order,variables):
    need(all(powers[0]>0 for powers in p),'binomial jet needs positive-order argument')
    out=term((0,)*variables);coefficient=Q(1)
    for k in range(1,order+1):
        coefficient*=Q(alpha-k+1,k)
        out=add(out,scale(power(p,k,order,variables),coefficient))
    return out


def coefficient(p,degree):
    return {powers[1:]:value for powers,value in p.items() if powers[0]==degree}


def records(p,names):
    return [{'powers':dict(zip(names,powers)),'coefficient':str(value)}
            for powers,value in sorted(p.items())]


def fourth_radial():
    # Variables are (w,s,j,p2). Keep the numerators through degree 4 because
    # division by exp(l*w)-1 lowers their first nonzero degree by one.
    nv=4;one=term((0,0,0,0));sw=term((1,1,0,0));jw=term((1,0,1,0))
    a=add(one,scale(exponential(scale(sw,-1),4,nv),-1))
    pref=logarithm(shift(a,(-1,-1,0,0)),3,nv)
    base={}
    for ell in range(1,5):
        # (exp(ell*w)-1)/(ell*w), followed by its formal reciprocal.
        normalized=add(*(term((h,0,0,0),Q(ell**h,factorial(h+1))) for h in range(4)))
        reciprocal=binomial(add(normalized,scale(one,-1)),-1,3,nv)
        numerator=shift(power(a,ell,4,nv),(-1,0,0,0))
        base=add(base,scale(multiply(numerator,reciprocal,3),Q(-1,ell**2)))
    siteproduct=multiply(add(exponential(sw,3,nv),scale(one,-1)),
                         add(one,scale(exponential(scale(jw,-1),3,nv),-1)),3)
    deleted=scale(logarithm(add(one,siteproduct),3,nv),-1)
    expected_deleted=add(term((2,1,1,0),-1),term((3,1,2,0),Q(1,2)),term((3,2,1,0),Q(-1,2)))
    need(deleted==expected_deleted,'individual deleted-site cubic jet differs')
    summed={}
    for (w,s,j,p2),value in deleted.items():
        need(j in (1,2),'unexpected site power')
        powers=(w,s+1,0,p2) if j==1 else (w,s,0,p2+1)
        summed=add(summed,term(powers,value))
    L=add(pref,base,term((0,1,0,0)),summed)
    expected=add(term((1,2,0,0),Q(1,4)),term((2,1,0,0),Q(-1,12)),
                 term((2,2,0,0),Q(-23,24)),term((2,3,0,0),Q(-1,36)),
                 term((3,3,0,0),Q(-1,2)),term((3,2,0,0),Q(-1,24)),term((3,1,0,1),Q(1,2)))
    need(L==expected,'normalized cubic logarithmic jet differs')
    fourth=shift(exponential(L,3,nv),(0,1,0,0))
    result=coefficient(fourth,3)
    expected_fourth={(7,0,0):Q(1,384),(6,0,0):Q(-1,144),(5,0,0):Q(-23,96),
                     (4,0,0):Q(-25,48),(3,0,0):Q(-1,24),(2,0,1):Q(1,2)}
    need(result==expected_fourth,'fourth radial integrand polynomial differs')
    # Under the alternating subset sum, s^m -> (-1)^(m+1) H^(m).
    h_coefficients={str(s):str(value*(-1)**(s+1)) for (s,j,p2),value in result.items() if p2==0}
    need(h_coefficients=={'7':'1/384','6':'1/144','5':'-23/96','4':'25/48','3':'-1/24'},
         'fourth radial derivative signs differ')
    return {'deleted_site_cubic_jet':records(deleted,('w','s','j','p2')),
            'normalized_log_cubic_jet':records(L,('w','s','j','p2')),
            's_times_T4':records(result,('s','j','p2')),
            'c4_H_derivative_coefficients':h_coefficients,
            'c4_marked_term':'(H L2)second_derivative / 2'}


def second_forward():
    # Variables (z,a,B,beta1,beta2), where z=n^(-1/2), a=sqrt(A).
    nv=5;one=term((0,0,0,0,0));p=term((2,0,0,0,0),Q(-1,24))
    prefactor=binomial(p,Q(-3,2),2,nv)
    sqrt_correction=add(binomial(p,Q(1,2),3,nv),scale(one,-1))
    exponent=shift(sqrt_correction,(-1,0,1,0,0))
    exponential_factor=exponential(exponent,2,nv)
    tau=shift(binomial(p,Q(-1,2),2,nv),(1,1,0,0,0))
    normalized=add(one,shift(tau,(0,0,0,1,0)),
                   shift(multiply(tau,tau,2),(0,0,0,0,1)))
    total=multiply(multiply(prefactor,exponential_factor,2),normalized,2)
    d1=coefficient(total,1);d2=coefficient(total,2)
    need(d1=={(1,0,1,0):Q(1),(0,1,0,0):Q(-1,48)},'first n-correction differs')
    need(d2=={(2,0,0,1):Q(1),(1,1,1,0):Q(-1,48),(0,0,0,0):Q(1,16),(0,2,0,0):Q(1,4608)},
         'second n-correction differs')
    return {'d1':records(d1,('sqrtA','B','beta1','beta2')),
            'd2':records(d2,('sqrtA','B','beta1','beta2'))}


def run():
    return {'status':'PASS','arithmetic':'Fraction sparse formal jets',
            'fourth_radial':fourth_radial(),'forward_n_corrections':second_forward(),
            'scope':'Exact finite algebra; analytic remainders and marked subset identity are proved in the report.'}


if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
