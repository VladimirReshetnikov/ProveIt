#!/usr/bin/env python3
"""Independent finite optimization checks for the accompanying article.

Dependencies: Python 3, NumPy, SciPy (HiGHS through scipy.optimize.linprog),
and SymPy. Run from the package root:
    python code/verify_fourier_lp.py --output data/verification_fourier_lp.json

The LPs are numerical diagnostics, not proofs or certified exact optimizers.
Three symbolic polynomial identities are checked separately with SymPy.
The continuous comparison discretizes the cosine interval; the finite-grid
comparisons use the actual allowed cyclic cosine nodes.
"""

import argparse
import json
from pathlib import Path


def check_continuous_profile():
    import json
    import numpy as np
    import sympy as s
    from scipy.optimize import linprog
    from scipy.optimize import brentq
    from numpy.polynomial.chebyshev import chebvander
    from math import cos, pi, sqrt
    c,v,x=s.symbols('c v x')
    F=4*(1-c)*(1+2*c)*v**3+4*c*(1-c)*(1+2*c)*v**2+(1+c)*(4*c*c-3)*v+c*(4*c*c-3)
    H=4*c*c*v*v-2*c*c*v-2*c*c-2*c*v*v-2*v*v+1
    q1=2*v*(c+v)**2;q2=(1-c*c-2*c*v-3*v*v)/2;q4=s.Rational(1,8)
    q0=s.Rational(3,8)-(c*c+2*c*v+3*v*v)/2-c*(c+2*v)*v*v
    r=(1+2*c*v)/(1-2*c-2*v);K=-q1-q2+q4
    Q=(c-x)*(-c-2*v-x)*(x-v)**2
    assert s.expand(Q-q0-q1*x-q2*(2*x*x-1)-q4*(8*x**4-8*x*x+1))==0
    assert s.factor((r*K+q0)*(1-2*c-2*v)*4-F)==0
    assert s.factor(s.resultant(F,H,v))==4*(c-1)**2*(c+1)**2*(2*c+1)**2*(4*c*c-2*c-1)**2
    P=lambda z:-1+5*z+11*z*z-6*z**3-12*z**4
    cs=brentq(P,0,1/6,xtol=1e-15); ast=np.arccos(cs)
    cf=s.lambdify((c,v),F,'numpy')
    def val(a):
     cc=cos(a)
     if a<=pi/5: return 0
     if a<=2*pi/5: return (1+2*cc-4*cc*cc)/(3+10*cc-12*cc*cc)
     if a<=ast: return (1-2*cc*cc)/(3+2*cc-4*cc*cc)
     if a<=3*pi/5:
      vv=brentq(lambda vv:cf(cc,vv),-1,-sqrt(3)/2,xtol=1e-14)
      return (1+2*cc*vv)/(1-2*cc-2*vv)
     if a<=5*pi/7: return 2*cc*(cc-1)/(2*cc*cc-2*cc+1)
     if a<=4*pi/5:
      z=-cc;t4=cos(4*(pi-a));return (z-t4)/(2-z-t4)
     return -cc
    rows=[]
    for aa in sorted(set(list(np.linspace(.05,.995,57))+[.2,.4,ast/pi,.5,.6,5/7,.8])):
     cc=cos(pi*aa);grid=np.linspace(-1,cc,10001);T=chebvander(grid,4)[:,1:].T
     A=np.hstack([np.vstack([T,-T]),-np.ones((8,1))]);tar=val(pi*aa)
     res=linprog(np.r_[np.zeros(len(grid)),1],A_ub=A,b_ub=np.zeros(8),A_eq=np.array([np.r_[np.ones(len(grid)),0]]),b_eq=[1.],bounds=[(0,None)]*(len(grid)+1),method='highs')
     assert res.success
     err=float(res.fun-tar)
     assert -1e-7<=err<=2e-6,(aa,tar,res.fun)
     rows.append({'a_over_pi':float(aa),'analytic':tar,'discrete_lp':float(res.fun),'excess':err})
    return {'transition_c':cs,'transition_a_over_pi':ast/pi,'symbolic_checks_passed':3,'LP_cases':len(rows),'max_discretization_excess':max(row['excess'] for row in rows),'rows':rows}


def check_finite_grids():
    import json
    from math import cos,sin,pi,sqrt,ceil,floor
    import numpy as np
    from scipy.optimize import linprog,brentq
    from numpy.polynomial.chebyshev import chebvander

    def F(c,v):return 4*(1-c)*(1+2*c)*v**3+4*c*(1-c)*(1+2*c)*v*v+(1+c)*(4*c*c-3)*v+c*(4*c*c-3)
    def cert(c,r,s):
     q1=(r+s)*(c+r)*(c+s)
     q2=(1-c*c-c*(r+s)-r*r-r*s-s*s)/2
     q0=-c*(c+r+s)*r*s+q2-1/8
     A=-q1-q2+1/8
     rho=-q0/A
     g=lambda x:2*x*x-x-1
     h=lambda x:8*x**4-8*x*x+1+x
     J=lambda x:h(x)*g(c)-g(x)*h(c)
     Jr,Js=J(r),J(s)
     th=Js/(Js-Jr)
     G=th*g(r)+(1-th)*g(s);p=G/(G-g(c))
     masses=np.array([p,(1-p)*th,(1-p)*(1-th)])
     moments=chebvander([c,r,s],4)[:,1:].T@masses
     conditions=(-c-r-s>c and q1<0 and q2<0 and -1e-10<=th<=1+1e-10 and G>0 and rho>0 and abs(moments[2])<=rho+1e-9)
     assert max(abs(moments-np.array([-rho,-rho,moments[2],rho])))<1e-8
     return rho,conditions,masses,moments

    def lp(N,a):
     lo=ceil(N*a/(2*pi)-1e-12)
     X=np.cos(np.arange(lo,N//2+1)*2*pi/N)
     T=chebvander(X,4)[:,1:].T
     A=np.hstack([np.vstack([T,-T]),-np.ones((8,1))])
     res=linprog(np.r_[np.zeros(len(X)),1.],A_ub=A,b_ub=np.zeros(8),A_eq=np.array([np.r_[np.ones(len(X)),0.]]),b_eq=[1.],bounds=[(0,None)]*(len(X)+1),method='highs')
     assert res.success
     return float(res.fun)
    rows=[]
    for N in range(8,241,4):
     j=(5*N)//12;r=cos(2*pi*(j+1)/N);s=cos(2*pi*j/N)
     value,good,m,ms=cert(0,r,s)
     assert good,(N,value,m,ms)
     opt=lp(N,pi/2)
     assert abs(value-opt)<2e-8,(N,value,opt)
     rows.append({'N':N,'value':value,'lp':opt})
    cs=brentq(lambda c:-1+5*c+11*c*c-6*c**3-12*c**4,0,1/6)
    checks=[];not_certified=[]
    for N in range(12,141):
     for frac in [.46,.48,.50,.53,.56,.59]:
      h=2*pi/N;an=h*ceil(frac*pi/h-1e-12);c=cos(an)
      if not (-(sqrt(5)-1)/4<c<cs):continue
      v=brentq(lambda v:F(c,v),-1,-sqrt(3)/2,xtol=1e-14)
      beta=np.arccos(v);j=floor(beta/h+1e-12);r=cos((j+1)*h);s=cos(j*h)
      if j+1>N//2 or not r<s<c or s>=-.5:continue
      value,good,m,ms=cert(c,r,s)
      if not good:not_certified.append([N,frac]);continue
      opt=lp(N,an)
      assert abs(value-opt)<2e-8,(N,frac,value,opt)
      rho=(1+2*c*v)/(1-2*c-2*v);p=(-rho-v)/(c-v)
      A=-(r+s)*(c+r)*(c+s)-(1-c*c-c*(r+s)-r*r-r*s-s*s)/2+1/8
      gap=(1-p)*(c-v)*(-c-r-s-v)/A*(v-r)*(s-v)
      assert abs(value-rho-gap)<1e-12
      checks.append({'N':N,'a_over_pi':frac,'rounded_a_over_pi':an/pi,'value':value,'lp':opt,'gap':gap})
    return {'aligned_cases':len(rows),'aligned_rows':rows,'general_valid_cases':len(checks),'general_rows':checks,'insufficient_certificate_cases':not_certified}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "data" / "verification_fourier_lp.json",
        help="Destination for the complete JSON verification record.")
    args = parser.parse_args(argv)
    result = {
        "schema_version": 1,
        "status": "all checks passed",
        "qualification": (
            "Supplementary independent implementation checks; numerical LP "
            "results are not mathematical proofs, proof-assistant verification, "
            "or external peer review."),
        "continuous_profile": check_continuous_profile(),
        "finite_grid": check_finite_grids(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "symbolic_identities": result["continuous_profile"]["symbolic_checks_passed"],
        "continuous_radii": result["continuous_profile"]["LP_cases"],
        "aligned_moduli": result["finite_grid"]["aligned_cases"],
        "general_grid_cases": result["finite_grid"]["general_valid_cases"],
        "output": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
