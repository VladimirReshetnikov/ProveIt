#!/usr/bin/env python3
"""Exact Sturm/interval certificate for the sixth-moment optimal phase.
All assertions use rational polynomial arithmetic, not numerical roots.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s
from verify_pressure import matrix

l,C=s.symbols('lambda C')
f=2048*l**5-128*(12*C*C+15*C+4)*l**4+40*(28*C**3+24*C*C+9*C+1)*l**3-(448*C**3+261*C*C-126*C+37)*l*l+(63*C*C+21*C-22)*l-2
fc=s.diff(f,C)
R=s.Poly(s.resultant(f,fc,l),C).sqf_part().primitive()[1]
if R.LC()<0:R=-R
sub=s.subresultants(f,fc,l)
content, primitive = s.Poly(sub[-2],l).primitive()
assert content == 169869312  # Nonzero constant: no exceptional specialization.
linear=primitive.as_expr()
A=s.Poly(s.expand(linear).coeff(l,1),C)
B=s.Poly(s.expand(linear).coeff(l,0),C)
assert s.degree(linear,l)==1
# Subresultants are polynomial combinations of f and f_C, so the
# primitive linear member vanishes at every common root. The content
# above is a nonzero integer, not a parameter-dependent divisor.
z=s.symbols('z', nonzero=True)
assert s.simplify(2048*matrix(3,z).charpoly(l).as_expr()
                 -f.subs(C,(z+1/z)/2)) == 0
chi2=l**3-(s.Rational(3,4)+C)*l*l+(s.Rational(1,4)+5*C/8)*l-s.Rational(1,8)
assert s.simplify(matrix(2,z).charpoly(l).as_expr()-chi2.subs(C,(z+1/z)/2))==0
assert chi2.subs(l,s.Rational(5,8))==-s.Rational(9,512)
cubic=64*l**3-20*l*l-6*l+1
assert s.rem(fc.subs(C,-1)-3*l*(720*l*l-196*l-41),cubic,l)==0
assert (720*l*l-196*l-41).subs(l,s.Rational(7,16))==s.Rational(177,16)


def plus(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):
    v=[x[0]*y[0],x[0]*y[1],x[1]*y[0],x[1]*y[1]]
    return min(v),max(v)
def ev(poly,box):
    v=(s.S.Zero,s.S.Zero)
    for a in poly.all_coeffs():v=plus(mul(v,box),(a,a))
    return v

def div(x,y):
    assert y[0]>0 or y[1]<0,'interval division includes zero'
    return mul(x,(1/y[1],1/y[0]))

def variation(x):
    vals=[s.sign(p.eval(x)) for p in sturm]
    vals=[v for v in vals if v]
    return sum(vals[j]!=vals[j-1] for j in range(1,len(vals)))

sturm=[s.Poly(p,C) for p in s.sturm(R.as_expr(),C)]
assert variation(-1)-variation(1)==4
boxes=[('-0.660930941723','-0.660930941722'),
       ('-0.070099130476','-0.070099130475'),
       ('-0.068679451074','-0.068679451073'),
       ('0.914028755782','0.914028755783')]
targets=[('0.430','0.431'),('-0.152','-0.150'),('-0.134','-0.132'),('0.229','0.231')]
rows=[]
for raw,target in zip(boxes,targets):
    box=tuple(s.Rational(x) for x in raw)
    assert variation(box[0])-variation(box[1])==1
    aa,bb=ev(A,box),ev(B,box)
    image=div((-bb[1],-bb[0]),aa)
    outer=tuple(s.Rational(x) for x in target)
    assert outer[0]<image[0] and image[1]<outer[1], (box,image,outer)
    rows.append({'C_interval':raw,'Sturm_variations':[variation(box[0]),variation(box[1])],
                 'stationary_eigenvalue_enclosure':target,
                 'interval_checked':True})
# Exact endpoint and separator identities.
sep=s.Rational(7,16)
p_third=8192*l**5+256*l**4-160*l**3-437*l**2-67*l-8
assert p_third.subs(l,sep)==s.Rational(405,64)
p_half=64*l**3-20*l**2-6*l+1
assert p_half.subs(l,sep)==-s.Rational(3,32)
assert s.expand(f.subs(C,-s.Rational(1,2))*4-p_third)==0
assert s.factor(f.subs(C,-1)-2*(16*l*l+4*l-1)*p_half)==0
output={'passed':True,'method':'exact rational Sturm sequence and rational interval Horner arithmetic',
        'linear_subresultant_content':str(content),
        'matrix_characteristic_identity_checked':True,
        'sturm_variations_at_minus_one_and_one':[variation(-1),variation(1)],
        'resultant_polynomial':str(R.as_expr()),'stationary_linear_A':str(A.as_expr()),
        'stationary_linear_B':str(B.as_expr()),'intervals':rows,
        'separator_at_7_over_16':['405/64','-3/32']}
Path('minimum_certificate.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
