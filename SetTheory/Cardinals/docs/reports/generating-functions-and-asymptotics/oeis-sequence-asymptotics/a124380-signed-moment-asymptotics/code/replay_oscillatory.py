#!/usr/bin/env python3
"""Finite exact oscillatory-sector coefficients, amplitude-scaled expansion.
The symbol p denotes pi, not a freely varying asymptotic parameter.
Requires SymPy. Prints JSON only; makes no network calls.
"""
import argparse, json
from functools import lru_cache
import sympy as s

def coefficients(order):
    L,y,p=s.symbols('L y p',real=True)
    mu=-(L+2)/4+s.I*p/4
    @lru_cache(None)
    def moment(d):
        if d==0:return s.Integer(1)
        if d==1:return mu
        return s.expand(mu*moment(d-1)+s.Rational(d-1,4)*moment(d-2))
    phase=[s.Integer(0)];Q=[s.Integer(1)];q=[s.Integer(1)]
    for j in range(1,order+1):
        corr=sum(s.bernoulli(2*r)/(2*r*(2*r-1))*s.binomial(j-1,2*r-2)*y**(j-2*r+1) for r in range(1,(j+1)//2+1))
        phase.append(s.expand((-1)**(j+1)*(2*y**(j+2)/(j+2)-y**(j+1)/(j*(j+1))+y**j/(2*j)+corr)))
        Q.append(s.expand(sum(ell*phase[ell]*Q[j-ell] for ell in range(1,j+1))/j))
        q.append(s.factor(sum(co*moment(ex[0]) for ex,co in s.Poly(Q[j],y).terms())))
    return L,y,p,phase,q

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--order',type=int,default=4);a=ap.parse_args()
    if a.order<0:ap.error('order must be nonnegative')
    L,y,p,phase,q=coefficients(a.order)
    print(json.dumps({'parameter':'x=sqrt(n/2), L=log(x); p=pi',
      'phase_polynomials':[str(z) for z in phase],
      'complex_coefficients':[str(z) for z in q],
      'sine_coefficients':[str(s.factor(s.re(s.expand(z)))) for z in q],
      'cosine_coefficients':[str(s.factor(s.im(s.expand(z)))) for z in q],
      'normalization':'J = Mminus*Im(exp(i theta)*sum(q_j/x^j)) + O(Mminus*(1+L)^(3R+3)/x^(R+1))',
      'Mminus':'exp(1/2-pi^2/8)*x*exp(x^2*(2L-1)-x*(L+1)+L^2/8)',
      'theta':'pi*x-pi*(L+2)/4','sympy_version':s.__version__},indent=2))
if __name__=='__main__':main()
