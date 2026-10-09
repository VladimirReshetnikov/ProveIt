#!/usr/bin/env python3
"""Exact symbolic compiler for the all-orders transition polynomials."""
from pathlib import Path
import json
import sympy as s


def polynomials(order: int):
    if order < 0:
        raise ValueError('order must be nonnegative')
    x,z,t,a,L=s.symbols('x z t a L')
    base=s.series(s.log(s.log(1+x)/x),x,0,order+2).removeO().expand()
    b={j:base.coeff(x,j) for j in range(1,order+2)}
    R=[s.Integer(0)]+[2**(j+1)*b[j+1]*z**(j+1)+s.Rational((-1)**j*2**j,j)*z**j for j in range(1,order+1)]
    Q=[s.Integer(1)]
    D=[s.Integer(0)]+[s.Rational((-1)**j,j+1)*(a**(j+1)-(a-t)**(j+1)) for j in range(1,order+1)]
    E=[s.Integer(1)]
    for n in range(1,order+1):
        Q.append(s.expand(sum(j*R[j]*Q[n-j] for j in range(1,n+1))/n))
        E.append(s.expand(sum(j*L*D[j]*E[n-j] for j in range(1,n+1))/n))
    def apply(poly,f):
        poly=s.Poly(poly,t); powers=[f]
        for _ in range(poly.degree()):
            powers.append(s.expand(z*powers[-1]-z*s.diff(powers[-1],z)))
        return s.expand(sum(coef*powers[m[0]] for m,coef in poly.terms()))
    P=[s.expand(sum(apply(E[n-k],Q[k]) for k in range(n+1))) for n in range(order+1)]
    assert s.simplify(P[1]-((z*z/2-(a+s.Rational(1,2))*z)*L+5*z*z/6-2*z))==0 if order>=1 else True
    return (a,L,z),P

if __name__=='__main__':
    vars,P=polynomials(4)
    out=Path(__file__).resolve().parents[1]/'results'
    out.mkdir(exist_ok=True)
    (out/'transition_polynomials.json').write_text(json.dumps({'variables':['a','L','z'],'P':[str(p) for p in P]},indent=2)+'\n')
    tex=[]
    for k,p in enumerate(P[:3]):
        tex.append(r'\begin{equation*}P_{'+str(k)+r'}(L,z;a)='+s.latex(s.collect(p,vars[1]))+r'.\end{equation*}')
    (out/'transition_polynomials.tex').write_text('\n'.join(tex)+'\n')
    print('P2 =',s.collect(P[2],vars[1]))
