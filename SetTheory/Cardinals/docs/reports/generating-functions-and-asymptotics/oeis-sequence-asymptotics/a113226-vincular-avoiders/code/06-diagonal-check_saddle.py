#!/usr/bin/env python3
"""Finite Gaussian-moment reconstruction of the asymptotic coefficients."""
import json,pathlib
import sympy as s
ROOT=pathlib.Path(__file__).resolve().parent
h,v=s.symbols('h v'); a,rho=s.symbols('a rho',positive=True)

def trunc(f,J): return s.series(f,h,0,J+1).removeO().expand()
def moment(f):
    p=s.Poly(s.expand(f),v)
    return s.simplify(sum(c*(s.factorial2(k-1) if k else 1)
                         for (k,),c in p.terms() if k%2==0))

def coefficients(K):
    J=2*K
    beta=s.sqrt(2/(3*a)); u=a*h**4*(1+s.I*beta*h*v); delta=rho*u
    # pi/sqrt(delta) = 2a h^-2 (1+i beta h v)^-1/2.
    core=trunc((1+s.I*beta*h*v)**s.Rational(-1,2),J+2)
    q=s.symbols('q')
    modular=s.series(((s.exp(q)-1)/q)**s.Rational(-1,2),q,0,(J+2)//4+2).removeO()
    T=trunc(2*a*h**(-2)*core*modular.subs(q,delta),J)
    # Remove the constant T0 and retain the analytic correction.
    T+=trunc(-delta/2-3*sum((-1)**j*(s.exp(delta)-1)**j/s.Integer(2*j+1)
                           for j in range(1,J//4+2)),J)
    logpart=trunc((h**(-6)+1)*sum(u**j/s.Integer(j) for j in range(1,(J+6)//4+2)),J)
    R=trunc(T+logpart-3*a/h**2+v**2/2,J)
    r=[s.expand(R).coeff(h,j) for j in range(J+1)]
    if r[0]!=0: raise RuntimeError(('constant failed',r[0]))
    e=[s.Integer(1)]
    for j in range(1,J+1):
        e.append(s.expand(sum(k*r[k]*e[j-k] for k in range(1,j+1))/j))
    for j in range(1,J+1,2):
        if moment(e[j])!=0: raise RuntimeError(('odd moment',j))
    return [s.factor(moment(e[2*j])) for j in range(K+1)]

if __name__=='__main__':
    cs=coefficients(3)
    expected=a*a*(1-rho)/2-s.Rational(5,36)/a
    if s.simplify(cs[1]-expected)!=0: raise RuntimeError('c1 mismatch')
    ar=(s.pi**2/(4*s.log(4)))**s.Rational(1,3)
    out={'status':'pass','order':3,'coefficients':[str(c) for c in cs],
         'numeric':[str(c.subs({a:ar,rho:s.log(4)}).evalf(30)) for c in cs]}
    (ROOT/'saddle_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
