#!/usr/bin/env python3
"""Exact identities and numerical illustrations for the Ehrhart critical windows.

Exact checks use SymPy rational polynomial arithmetic. Numerical collision values
use stable real recurrences; they are illustrations, not certificates or substitutes
for the analytic proof. Run from any directory with Python, sympy, scipy installed.
"""
import argparse, itertools, json, math, pathlib
import sympy as sp
from scipy.optimize import root_scalar

s, t = sp.symbols('s t')

def binpoly(x,k):
    return sp.prod(x-j for j in range(k))/sp.factorial(k)

def exact_h(d):
    return sp.Poly(sp.expand(sum(sp.binomial(d,k)*sp.binomial(d+k,k)*binpoly(s,k)
                                 for k in range(d+1))),s,domain=sp.QQ)

def exact_c(d):
    return sp.Poly(sp.expand(sum(2**k*sp.binomial(d,k)*binpoly(s,k)
                                 for k in range(d+1))),s,domain=sp.QQ)

def exact_checks():
    checks = {'dimension_recurrences':0,'hstar_identity':0,'reflection':0,
              'lattice_counts':0,'symbolic_normal_forms':0}
    H=[exact_h(d) for d in range(15)]
    C=[exact_c(d) for d in range(15)]
    for d in range(1,14):
        assert ((d+1)**2*H[d+1] - sp.Poly((2*d+1)*(2*s+1),s)*H[d]-d*d*H[d-1]).is_zero
        assert ((d+1)*C[d+1] - sp.Poly(2*s+1,s)*C[d]-d*C[d-1]).is_zero
        checks['dimension_recurrences']+=2
    for d in range(2,13):
        D=(C[d]-C[d-2]).mul_ground(sp.Rational(1,2))
        for M in range((d+1)//2+1):
            E=H[d]-M*D
            # Direct Ehrhart-series numerator: complete graph minus 2 M t(1+t)^(d-2).
            hp=[sp.binomial(d,j)**2-2*M*sp.binomial(d-2,j-1) for j in range(d+1)]
            p=sp.Poly(sp.expand(sum(hp[j]*binpoly(s+d-j,d) for j in range(d+1))),s)
            assert (E-p).is_zero
            checks['hstar_identity']+=1
            assert (sp.Poly(E.as_expr().subs(s,-1-s),s)-(-1)**d*E).is_zero
            checks['reflection']+=1
    # Independent integer-point count using the complete-multipartite gauge.
    for v in range(3,7):
        d=v-1
        for M in range(v//2+1):
            E=H[d]-sp.Rational(M,2)*(C[d]-C[d-2])
            for k in range(3):
                count=0
                for initial in itertools.product(range(-k,k+1),repeat=v-1):
                    x=initial+(-sum(initial),)
                    if abs(x[-1])>k or sum(max(a,0) for a in x)>k:
                        continue
                    if any(abs(x[2*j])+abs(x[2*j+1])>k for j in range(M)):
                        continue
                    count+=1
                assert count==E.eval(k),(v,M,k,count,E.eval(k))
                checks['lattice_counts']+=1
    eps,h,V,x,alpha,g,l,p=sp.symbols('eps h V x alpha g l p')
    a1=2*g+4*l; b1=g+3*l-2
    a2=a1*a1/2-p*p/2; b2=b1*b1/2-p*p/4-2
    CC=g+sp.Rational(5,3)*l+sp.Rational(2,3)
    beta=2-l; kap=p*p/4-2+sp.Rational(2,3)*beta*beta
    assert sp.expand((2*a1-b1)/3-CC)==0
    assert sp.expand((3*CC**2-2*(a2-b2))/2-kap)==0
    assert sp.expand(a1-2*b1-2*beta)==0
    checks['symbolic_normal_forms']+=3
    # Independent truncated exponential products, even case.
    z=sp.I*h*eps+V*eps**2; v=V*eps
    ap=1+a1*z+a2*z*z; am=1-a1*z+a2*z*z
    bp=1+b1*z+b2*z*z; bm=1-b1*z+b2*z*z
    even=ap*(1+2*v+2*v*v)+am*(1-2*v+2*v*v)-(1+alpha*eps**2)*(bp*(1+v+v*v/2)+bm*(1-v+v*v/2))
    coeff=sp.expand(even).coeff(eps,2)
    target=3*(V+sp.I*h*CC)**2-2*(alpha-kap*h*h)
    assert sp.expand(coeff-target)==0
    checks['symbolic_normal_forms']+=1
    # Odd case, eps=L^(-1/3); z=u/L and v=u-i h.
    z=sp.I*h*eps**3+sp.I*x*eps**4; v=sp.I*x*eps
    ep=lambda r: 1+r*v+(r*v)**2/2+(r*v)**3/6
    odd=(1+a1*z)*ep(2)-(1-a1*z)*ep(-2)-2*(1+alpha*eps**2)*((1+b1*z)*ep(1)-(1-b1*z)*ep(-1))
    coeff=sp.expand(odd).coeff(eps,3)
    assert sp.expand(-coeff/(2*sp.I)-(x**3+2*alpha*x-2*beta*h))==0
    checks['symbolic_normal_forms']+=1
    assert sp.expand(sp.discriminant(x**3+2*alpha*x-2*beta*h,x)+32*alpha**3+108*beta**2*h*h)==0
    checks['symbolic_normal_forms']+=1
    return checks

def evaluate(d,t):
    """Return rotated H,D and their first two t derivatives, in binary64.

    Rotating by i^(-d) keeps all recurrence arithmetic real. D is formed
    from the recurrence to avoid subtracting two nearly equal C values.
    """
    hm2=(1.,0.,0.); hm1=(2.*t,2.,0.)
    cm2=(1.,0.,0.); cm1=(2.*t,2.,0.)
    if d<2: raise ValueError('d must be at least two')
    for n in range(1,d):
        A=2.*(2*n+1)/(n+1)**2; B=(n/(n+1))**2
        h=(A*t*hm1[0]-B*hm2[0],
           A*(hm1[0]+t*hm1[1])-B*hm2[1],
           A*(2*hm1[1]+t*hm1[2])-B*hm2[2])
        a=2./(n+1); b=n/(n+1)
        c=(a*t*cm1[0]-b*cm2[0],
           a*(cm1[0]+t*cm1[1])-b*cm2[1],
           a*(2*cm1[1]+t*cm1[2])-b*cm2[2])
        if n==d-1:
            D=((2*t*cm1[0]+cm2[0])/(2*d),
               (2*cm1[0]+2*t*cm1[1]+cm2[1])/(2*d),
               (4*cm1[1]+2*t*cm1[2]+cm2[2])/(2*d))
        hm2,hm1=hm1,h;cm2,cm1=cm1,c
    return hm1,D

def collision(d,j=0):
    h=(2*j+1)*math.pi;L=math.log(d);beta=2-math.log(2)
    CC=float(sp.EulerGamma)+5*math.log(2)/3+2/3
    kap=math.pi**2/4-2+2*beta**2/3;cstar=math.sqrt(8/math.pi)
    if d%2==0:
        guess=h/(L+CC)
    else:
        guess=h/(L+CC)-(beta*h)**(1/3)/(L+CC)**(4/3)
    def func(z):
        H,D=evaluate(d,z)
        return H[1]*D[0]-H[0]*D[1]
    def dfunc(z):
        H,D=evaluate(d,z)
        return H[2]*D[0]-H[0]*D[2]
    sol=root_scalar(func,fprime=dfunc,x0=guess,method='newton',xtol=2e-13,maxiter=40)
    if not sol.converged:raise RuntimeError((d,sol))
    tt=sol.root;H,D=evaluate(d,tt);M=H[0]/D[0]
    if d%2==0:
        alpha=(M/(cstar*math.sqrt(d))-1)*L*L
        target=kap*h*h
        scaled_t=(tt-h/L)*L*L
        target_t=-h*CC
    else:
        alpha=(M/(2*cstar*math.sqrt(d))-1)*L**(2/3)
        target=-1.5*(beta*h)**(2/3)
        scaled_t=(tt-h/L)*L**(4/3)
        target_t=-(beta*h)**(1/3)
    return dict(d=d,parity='even' if d%2==0 else 'odd',h=h,collision_M=M,
                collision_height=tt,scaled_parameter=alpha,limiting_parameter=target,
                scaled_height_correction=scaled_t,limiting_height_correction=target_t,
                W_residual=func(tt),iterations=sol.iterations,
                kind='numerical illustration, binary64; not a certificate')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-power',type=int,default=4)
    parser.add_argument('--output',default=str(pathlib.Path(__file__).with_name('critical_ehrhart_checks.json')))
    args=parser.parse_args()
    checks=exact_checks();print('EXACT',json.dumps(checks),flush=True)
    rows=[]
    for power in range(2,args.max_power+1):
        for d in [10**power,10**power+1]:
            row=collision(d);rows.append(row);print(json.dumps(row),flush=True)
    data={'exact_checks':checks,'numeric_collision_illustrations':rows}
    pathlib.Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
