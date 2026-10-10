#!/usr/bin/env python3
"""Independent formal coefficient checks. Requires SymPy; not a proof assistant."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import sympy as S


def run() -> dict:
    s,e=S.symbols('s e')
    mu,q2,q3,q4,q5=S.symbols('mu q2 q3 q4 q5')
    raw=[1,mu,q2,q3,q4,q5]
    central=lambda p:S.expand(sum(S.binomial(p,j)*(-mu)**(p-j)*raw[j]
                                 for j in range(p+1)))
    M2,M3,M5=central(2),central(3),central(5)
    k1=-2*M3
    k2=3*M5-(12*M2+2*mu**2)*M3
    # Chebyshev recurrence uses Re(z)=s*eta and |z|^2=s.
    P=[S.Integer(0),S.Integer(1)]
    for n in range(2,8):
        P.append(S.expand(2*s*e*P[-1]-s*P[-2]))
    J=sum(S.Rational(n-1,2)*raw[n-2]*P[n] for n in range(2,8))
    expr=S.series((J/s).subs(e,mu+k1*s+k2*s**2),s,0,3).removeO()
    assert S.expand(expr)==0
    U,V,W=S.symbols('U V W')
    explicit_M3=M3.subs({mu:U/3,q2:V/6,q3:W/10})
    assert S.expand(-2*explicit_M3-(U*V/3-W/5-4*U**3/27))==0
    # General Student exponent, computed in centered coordinates.
    h,p=S.symbols('h p')
    M2s,M3s,M5s=S.symbols('M2 M3 M5')
    aa=-p*M3s
    bb=p*(p+1)*M5s/2-3*p**2*M2s*M3s
    # E[(V-delta)(1+(V-delta)^2 h)^(-p)] to h^2.
    delta=aa*h+bb*h**2
    expr2=-delta-p*h*(M3s-3*delta*M2s-delta**3)
    expr2+=p*(p+1)/2*h**2*M5s
    assert S.expand(S.series(expr2,h,0,3).removeO())==0
    # Half-shift closed forms differentiated after z=r^2.
    r=S.symbols('r',positive=True)
    A=S.atanh(r)
    fm=2*A**2-4*r*A-2*S.log(1-r**2)
    fp=2*A**2+2*S.log(1-r**2)
    assert S.simplify(S.diff(fm,r)-4*r**2*A/(1-r**2))==0
    assert S.simplify(S.diff(fp,r)-4*(A-r)/(1-r**2))==0
    return {'status':'PASS','sympy_version':S.__version__,
      'checks':[
       'Normalized angular equation through rho^4 in five independent raw moments',
       'K(1,b)=-2 times the third central moment',
       'General Student mode expansion through y^-4',
       'Derivative of the negative-half-shift closed form',
       'Derivative of the positive-half-shift closed form'],
      'quartic_coefficient_raw_moments':str(S.expand(k2))}


def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    a=ap.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    p=a.output_dir/'symbolic-results.json'
    if p.exists():raise FileExistsError(p)
    result=run();p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
