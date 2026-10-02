#!/usr/bin/env python3
"""Finite exact combinatorial and numerical checks; not proof of the all-depth theorem."""
from fractions import Fraction as F
import json
import math


def comps(total,n):
    if n==1:
        yield (total,)
    else:
        for a in range(total+1):
            for tail in comps(total-a,n-1):yield (a,)+tail

kernel_cases=0
for j in range(2,9):
    widths=[F(1,2**i) for i in range(1,j+1)]
    L=F(3,4)-F(1,2**j)
    for k in range(1,j):
        for orders in comps(k,j):
            index=next(i for i,h in enumerate(orders) if h==0)
            remaining=[i for i in range(j) if i!=index]
            assert len(remaining)==j-1
            assert sum(orders[i] for i in remaining)<=j-1
            digit_radius=F(1,4)+(widths[index]-widths[-1])/2
            support_radius=digit_radius+sum((widths[i]/2 for i in remaining),F(0))
            assert support_radius==L
            assert widths[index]/widths[-1]==2**(j-index-1)
            kernel_cases+=1

def triangle_value(x,center,width):
    return max(F(0),F(1)-abs(x-center)/width)

def moment(r,y,center,width):
    if r==0:return triangle_value(y,center,width)
    out=F(0)
    # f(y+t)=slope*t+intercept on each segment.
    for lo,hi,slope,intercept in [
        (center-width-y,center-y,1/width,1+(y-center)/width),
        (center-y,center+width-y,-1/width,1-(y-center)/width),
    ]:
        lo=max(F(0),lo)
        if hi<=lo:continue
        out += slope*(hi**(r+1)-lo**(r+1))/(r+1)+intercept*(hi**r-lo**r)/r
    return out/math.factorial(r-1)

interpolation_checks=0
for center in [F(0),F(1,3),F(1),F(3)]:
    for width in [F(1,4),F(1),F(2)]:
        M=float(1/width)
        for y in [F(-1),F(0),F(1,5),F(1,2),F(2)]:
            for r in range(1,9):
                Hr=float(moment(r,y,center,width))
                for ell in range(r):
                    Hl=float(moment(ell,y,center,width))
                    A=math.factorial(r+1)**(1/(r+1))
                    if ell:
                        A=A/math.factorial(ell)+1/((ell+1)*math.factorial(ell-1))+math.factorial(r-1)/math.factorial(ell-1)
                    rhs=A*M**((r-ell)/(r+1))*Hr**((ell+1)/(r+1))
                    assert Hl<=rhs+1e-10*(1+rhs)
                    interpolation_checks+=1

def sinc_pi(x):
    if x==0:return 1.
    n=round(x)
    return (-1)**n*math.sin(math.pi*(x-n))/(math.pi*x)

P=math.prod(sinc_pi(2**(-ell)) for ell in range(1,100))
rows=[]
for j in range(1,9):
    product=math.prod(((-1)**(2**(j-i))*2*i) for i in range(1,j+1))
    assert F(product,2**j)==-math.factorial(j)
    for sign in [-1,1]:
        delta=sign*1e-5;q=.5+delta;T=2**j
        derivative=math.prod(sinc_pi(T*q**i) for i in range(1,100))/T
        ratio=derivative/delta**j
        expected=-math.factorial(j)*P
        assert abs(ratio/expected-1)<.02
        rows.append({'j':j,'delta':delta,'scaled_defect':ratio,'predicted_limit':expected})

out={
 'status':'PASS',
 'scope':'Exact finite Leibniz extraction/support cases and scalar coefficients; numerical interpolation/product regressions only',
 'exact_kernel_cases':kernel_cases,
 'interpolation_checks':interpolation_checks,
 'P_truncation_l1_to99':P,
 'defect_rows':rows,
 'not_computed':['optimal distances','all-depth analytic proof by a proof assistant','weighted-integral maxima','upper constants','one-sided order-j limits'],
}
print(json.dumps(out,indent=2))
