"""Optional exact symbolic regressions; requires SymPy.
The universal statements are proved in the article, not inferred from tests.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]

def main():
    if not __debug__:raise RuntimeError('Do not run verifiers with python -O')
    c,t=s.symbols('c t');p=s.symbols('p0:24')
    def P(k):return sum((-1)**j*s.binomial(k+1,j)*(2*c)**(k+1-j)*p[k+2+j] for j in range(k+2))
    for j in range(10):
        n=2*j+3
        d=sum((-c)**(n-k)*s.binomial(n-1,k-1)*p[k] for k in range(2,n+1))
        transported=sum((-1)**(k+1)*s.binomial(j+1,k+1)*c**(2*(j-k))*P(k) for k in range(j+1))
        assert s.expand(d-transported)==0
    # Divided differences in the elementary symmetric coordinates s=2tc,p=t.
    h=[s.Integer(1),2*t*c]
    for n in range(2,23):h.append(s.expand(2*t*c*h[-1]-t*h[-2]))
    psi=s.expand(sum(p[n]*h[n-1]/t for n in range(2,24)))
    for k in range(10):assert s.expand(psi.coeff(t,k)-P(k))==0
    # Coefficients through rho^6, retaining an independent symbol mu.
    mu=s.symbols('mu');K,Q,R=s.symbols('K Q R')
    pp={p[3]:2*p[2]*mu}
    A=P(1).subs(c,mu).subs(pp);B=P(2).subs(c,mu).subs(pp);C=P(3).subs(c,mu).subs(pp)
    A1=s.diff(P(1),c).subs(c,mu).subs(pp);B1=s.diff(P(2),c).subs(c,mu).subs(pp)
    kv=-A/(2*p[2]);qv=-(A1*K+B)/(2*p[2]);rv=-(A1*Q+4*p[3]*K*K+B1*K+C)/(2*p[2])
    eta=mu+K*t+Q*t*t+R*t**3
    expr=sum(P(k).subs(c,eta) * t**k for k in range(4))
    expr=s.series(expr,t,0,4).removeO().expand().subs(pp)
    assert s.simplify(expr.coeff(t,1).subs(K,kv))==0
    assert s.simplify(expr.coeff(t,2).subs(Q,qv))==0
    assert s.simplify(expr.coeff(t,3).subs(R,rv.subs(pp)))==0
    # Bernstein certificates imported from the audited quadratic-threshold proof.
    x=s.symbols('x');bern=[s.Rational(233,1458),s.Rational(233,1458),s.Rational(367,2430),s.Rational(665,5832),s.Rational(55,486),s.Rational(95,1458),s.Rational(41,729)]
    P6=(800*x**6-2025*x**5+1833*x**4-567*x**3-192*x*x+233)/1458
    assert s.expand(sum(b*s.binomial(6,j)*x**j*(1-x)**(6-j) for j,b in enumerate(bern))-P6)==0
    assert all(b>0 for b in bern)
    doc={'status':'PASS','mobius_transport_orders':list(range(10)),
         'chebyshev_polynomials_checked':list(range(10)),
         'radial_coefficients_checked':['K','Q','R'],'quadratic_threshold_bernstein':True,
         'sympy_version':s.__version__,'scope':'finite regression checks, not proof by extrapolation'}
    (ROOT/'certificates/symbolic_verified.json').write_text(json.dumps(doc,indent=2)+'\n')
    print(json.dumps(doc,indent=2))
if __name__=='__main__':main()
