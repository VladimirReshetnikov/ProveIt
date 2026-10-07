#!/usr/bin/env python3
"""Exact rational certificates for the elementary inequalities in Report 222.
This proves the stated bounds, NOT an effective asymptotic onset.
"""
from fractions import Fraction as Q
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def exp_upper(x):
    """e^x <= 1+x+x^2/(2(1-x/3)), 0<=x<3, from k!>=2*3^(k-2)."""
    require(0 <= x < 3, 'exponential bound domain')
    return 1 + x + x*x/(2*(1-x/3))


def verify():
    tests = []
    def lt(value, limit, name):
        require(value < limit, name)
        tests.append({'bound': name, 'upper_rational': str(value), 'strict_limit': str(limit)})
    # sum r^j U^(j-1)/j <= r+r^2 U/[2(1-rU)].
    r, U, Z = Q(1,5), Q(1,20), Q(9,20)
    A = r+r*r*U/(2*(1-r*U))
    lt(A, Q(202,1000), 'unmarked A')
    E = exp_upper(2*A)
    lt(E, Q(1499,1000), 'unmarked ball')
    lt(A*E, Q(303,1000), 'unmarked contraction')
    W = Z*Z*U
    lt(2*r/(r-W), Q(11,5), 'unmarked derivative')
    lt(Z*Z*U/(1-Z*U), Q(11,1000), 'unmarked R')
    lt(Q(11,5)*Z*U/(1-Z*U), Q(51,1000), 'unmarked R_z')
    E = exp_upper(Q(11,1000))
    lt(Z*(E-1), Q(5,1000), 'unmarked zeta displacement')
    lt(E-1+Z*E*Q(51,1000), Q(4,100), 'unmarked zeta derivative')
    # e > 1+1+1/2+1/6=8/3; e < 1+1+sum_{k>=2}1/(2*3^(k-2))=11/4<3.
    require(Q(11,4) < 3, 'e upper bound')
    lt(Q(11,10)*(Q(3,8)+Q(1,100)), Z, 'normalized disk containment')
    for delta in (Q(4,100), Q(2,100)):
        lt(Q(1,100)/(Q(1,3)-Q(1,100))+delta/(1-delta), Q(1,10), 'cut argument sum')
    require(Q(1,10) < Q(1,2), '1/10 < pi/6 since pi>3')
    U=Q(1,100)
    def eta(s): return 2*s*s/(1-s)
    A=r+r*r*U/(2*(1-r*U))
    lt(A,Q(201,1000),'marked A')
    s=r*U
    D=2*r*r*U/((1-s)*(1-eta(s)))
    lt(D,Q(802,1000000),'marked small D')
    E=exp_upper(2*A+D)
    lt(E,Q(3,2),'marked ball')
    lt(A*E,Q(302,1000),'marked contraction')
    W=Z*Z*U; s=Z*U
    lt(2*r/(r-W),Q(21,10),'marked derivative')
    lt(eta(s),Q(41,1000000),'marked eta')
    lt(Z*Z*U/(1-s),Q(2035,1000000),'marked recursive R')
    lt(Q(21,10)*s/(1-s),Q(95,10000),'marked recursive derivative')
    lt(2*Z*Z*U/((1-s)*(1-eta(s))),Q(4069,1000000),'marked D')
    lt(2*s*(2-s)/((1-s)**2*(1-eta(s))),Q(182,10000),'marked D_z')
    lt(Q(2035+4069,1000000),Q(62,10000),'marked R total')
    lt(Q(95+182,10000),Q(28,1000),'marked R_z total')
    E=exp_upper(Q(62,10000))
    lt(Z*(E-1),Q(28,10000),'marked zeta displacement')
    lt(E-1+Z*E*Q(28,1000),Q(2,100),'marked zeta derivative')
    require(s*(2+s) <= 2*s*(2-s), 'B derivative dominated')
    return {'status':'pass','arithmetic':'exact rational arithmetic only','scope':'Elementary domain bounds; no asymptotic onset certificate','inequalities':tests}


if __name__=='__main__':
    print(json.dumps(verify(),indent=2,sort_keys=True))
