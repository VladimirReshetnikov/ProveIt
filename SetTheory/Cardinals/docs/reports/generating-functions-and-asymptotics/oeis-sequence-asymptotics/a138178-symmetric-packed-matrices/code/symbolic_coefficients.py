#!/usr/bin/env python3
"""Two independent exact symbolic derivations; a finite algebraic verifier."""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import argparse
import sympy as sp
from common import emit, new_file_path, require


def verify():
    h,y,w,L,v,a,c=sp.symbols('h y w L v a c',real=True)
    rho=1-v*h/2+v*v*h*h/8
    B=(a*L*rho**2*sp.exp(2*sp.I*h*w)/(1+h*y)
       +c*L**2*rho**4*sp.exp(4*sp.I*h*w)/(1+h*y)**2
       +h*v**3*L**2*rho**3*sp.exp(3*sp.I*h*w)/(3*(1+h*y)**2)
       +h*h*((v**4-1)*L**3/4+L**4/6))
    B=sp.series(B,h,0,3).removeO().expand()
    def gaussian(poly):
        result=0
        for (i,j),coefficient in sp.Poly(sp.expand(poly),y,w).terms():
            if i%2 or j%2:continue
            mi=sp.factorial2(i-1) if i else 1
            mj=sp.factorial2(j-1)/2**(j//2) if j else 1
            result+=coefficient*mi*mj
        return sp.factor(result)
    B1=B.coeff(h,1); B2=B.coeff(h,2)
    G1=y**3/3; H1=v*w*w/2-2*sp.I*w**3/3
    generalized_C1=gaussian(B1)
    require(sp.expand(generalized_C1-(-v*(a*L+2*c*L**2)+v**3*L**2/3))==0,'collision C1 mismatch')
    base={a:(v*v-1)/2,c:sp.Rational(1,4)}
    C1=sp.factor(generalized_C1.subs(base))
    C2=sp.factor(gaussian(B2+(G1+H1)*B1+B1**2/2).subs(base)-gaussian(G1+H1)*C1)
    D2=sp.factor(C2-C1**2/2)
    target1=-v*(v*v-1)*L/2+v*(2*v*v-3)*L**2/6
    target2=v*v*(v*v-1)*(L+L**3)/4+(-5*v**4+6*v*v-3)*L**2/8+L**4/24
    require(sp.expand(C1-target1)==0,'Gaussian C1 mismatch')
    require(sp.expand(D2-target2)==0,'Gaussian logarithmic C2 mismatch')
    # Independent factorial-degree-moment calculation from the atom expansion.
    aa=(v*v-1)/2; b=v**3/3; d=(v**4-1)/4; J=aa*L+L**2/2
    alternative1=-v*J+b*L**2
    alternative2=(aa*(J*J+aa*L+L**2)+J/2-v*b*L**2*(J+sp.Rational(3,2))
                  +b*b*L**4/2+d*L**3+L**4/6)
    require(sp.expand(C1-alternative1)==0 and sp.expand(C2-alternative2)==0,
            'independent factorial-moment coefficients mismatch')
    require(sp.expand(C2.subs(v,1)-(-L**2/4+L**4/18))==0,'unmarked C2 mismatch')
    collision_w,collision_z=sp.symbols('collision_w collision_z')
    collision=sp.expand(generalized_C1.subs({a:(v*v-1)/2+(collision_w-1)*v*v,
                                           c:(2*collision_z-1)/4}))
    require(sp.expand(collision.subs({collision_w:1,collision_z:1})-C1)==0,'unit collision specialization')
    binary=sp.expand(collision.subs({collision_w:0,collision_z:0}))
    require(sp.expand(binary-(v*(v*v+1)*L/2+(v/2+v**3/3)*L**2))==0,'binary C1 mismatch')
    difference=sp.expand((collision-C1).subs(v,1))
    require(sp.expand(difference-(L*(1-collision_w)+L**2*(1-collision_z)))==0,'Poisson mean correction mismatch')
    # Involution-ratio coefficients from the exact recurrence, separately from the saddle.
    x=sp.symbols('x'); coefficients=sp.symbols('a1:5')
    ratio=x*(1+sum(coefficients[i-1]*x**i for i in range(1,5)))
    previous=sp.series(ratio.subs(x,x/sp.sqrt(1-x*x)),x,0,7).removeO()
    equation=sp.series(ratio*(v+(x**-2-1)*previous)-1,x,0,5).removeO()
    solution={}
    for i in range(1,5):
        candidates=sp.solve(equation.coeff(x,i).subs(solution),coefficients[i-1])
        require(len(candidates)==1,'involution coefficient not uniquely determined')
        solution[coefficients[i-1]]=sp.factor(candidates[0])
    logratio=sp.series(sp.log((ratio/x).subs(solution)),x,0,5).removeO()+sp.log(x)
    c1,c2=sp.symbols('c1 c2')
    F=-sp.log(x)/x**2-sp.Rational(1,2)/x**2+v/x+c1*x+c2*x*x
    delta=sp.series(F-F.subs(x,x/sp.sqrt(1-x*x))+logratio,x,0,5).removeO()
    solved=sp.solve([sp.expand(delta).coeff(x,i) for i in (3,4)],[c1,c2])
    require(sp.expand(solved[c1]-(v**3/24+v/4))==0,'involution log C1')
    require(sp.expand(solved[c2]-(-v**2/16-sp.Rational(1,12)))==0,'involution log C2')
    # Rational certificate needed to identify the positive part in the TV constant:
    # log 2 = 2 sum_{j>=0} (1/3)^(2j+1)/(2j+1), with geometric tail bound.
    lower=2*sum(sp.Rational(1,3)**(2*j+1)/(2*j+1) for j in range(8))
    upper=lower+2*sp.Rational(1,3)**17/(17*(1-sp.Rational(1,9)))
    require(lower>0 and lower+lower**2>1 and upper+upper**2<2,'TV positive-part range certificate')
    return {'status':'PASS','scope':'Exact symbolic identities and a rational log(2) enclosure; not asymptotic remainder certification',
            'C1':str(C1),'C2':str(C2),'log_C2':str(D2),'collision_C1':str(collision),
            'binary_C1':str(binary),'collision_C1_difference_at_v1':str(difference),
            'involution_log_C1':str(solved[c1]),'involution_log_C2':str(solved[c2]),
            'log2_lower':str(lower),'log2_upper':str(upper),'certified_1_lt_log2_plus_log2_squared_lt_2':True,
            'methods':['coupled Gaussian saddle moments','factorial-degree moments','involution recurrence'],
            'sympy_version':sp.__version__}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output');a=p.parse_args()
    if a.output is not None:new_file_path(a.output)
    emit(verify(),a.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
