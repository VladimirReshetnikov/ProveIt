#!/usr/bin/env python3
"""Four-witness, seven-square certificate for the explicit binary shuttle.

External natural gap parameter x means initial gap d=7+x. No generic chart
parameter sharing is claimed: the two explicit charts have affine differences.
"""
from exact_phase_quartic import Poly,Certificate,integer


def compact_binary_uniform_sos():
    arity=10
    x,t,x0,x1,x2,x3,e,n,j,u=(Poly.var(arity,k) for k in range(arity))
    d=7+x
    T=n*n+(2*d-11)*n
    residuals=(e*(e-1),d+n-6-j-u,
        t-(T+j+e*(d+n-5)),x0,
        x1-(3+j+e*(d+n-7-2*j)),
        x2-(4+j+e*(d+n-6-2*j)),
        x3-(d+n+e))
    expression=sum((r*r for r in residuals),Poly.const(arity,0))
    return Certificate((),6,('e','n','j','u'),(),residuals,(),expression,'sos',(0,1))


def compact_binary_witness(x,side,n,j):
    for value,name in ((x,'gap parameter'),(side,'side'),(n,'cycle'),(j,'flight parameter')):
        integer(value,name,True)
    if side not in (0,1):
        raise ValueError('side must be 0 (right) or 1 (left)')
    u=1+x+n-j
    if u<0:
        raise ValueError('flight parameter is outside the half-open phase interval')
    return (side,n,j,u)
