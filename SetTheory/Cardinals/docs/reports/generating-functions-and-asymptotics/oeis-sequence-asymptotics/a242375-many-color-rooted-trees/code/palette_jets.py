#!/usr/bin/env python3
"""Optional SymPy finite palette generator. No network or global settings."""
import argparse
import json
from colored_trees import integer, counts, parse_small


def generate(M=4):
    integer(M,'M',1,6)
    try:
        import sympy as s
    except ImportError as exc:
        raise RuntimeError('Optional palette generation requires SymPy') from exc
    u,z,a=s.symbols('u z a')
    out={}
    for sign in (1,-1):
        eps=lambda j:1 if sign==1 else (-1)**(j-1)
        f=[s.S(0),s.S(1)]
        for n in range(2,M+2):
            f.append(s.expand(sum(f[n-j]*sum(d*f[d]*u**(j-d)*eps(j//d) for d in range(1,j+1) if j%d==0) for j in range(1,n))/(n-1)))
        R=s.expand(sum(s.Rational(eps(j),j)*f[m]*z**(j*m)*u**(m*(j-1)) for j in range(2,M+2) for m in range(1,M//(j-1)+1)))
        R=s.series(R,u,0,M+1).removeO()
        def at_radius(expr,S):
            ans=0
            for (zp,up),c in s.Poly(s.expand(expr),z,u).terms():
                if up<=M:
                    ans+=c*a**zp*u**up*s.series(s.exp(-zp*S),u,0,M+1-up).removeO()
            return s.series(ans,u,0,M+1).removeO().expand()
        S=s.S(0)
        for j in range(1,M+1):
            S+=s.factor(at_radius(R,S).coeff(u,j))*u**j
        B=1+at_radius(z*s.diff(R,z),S)
        H=s.series(s.log(B)/2,u,0,M+1).removeO().expand()
        D=s.series(s.exp(S),u,0,M+1).removeO().expand()
        c=at_radius(z*z*(s.diff(R,z)**2+s.diff(R,z,2))+2*z*s.diff(R,z),S)
        d1=s.series(s.Rational(11,24)*(1-B)+s.Rational(3,8)*c/B,u,0,M+1).removeO().expand()
        out['all' if sign==1 else 'identity']={
            'f':[str(v) for v in f], 'R':str(R),
            'S':[str(s.factor(S.coeff(u,j))) for j in range(1,M+1)],
            'log_H':[str(s.factor(H.coeff(u,j))) for j in range(1,M+1)],
            'growth_over_eq':[str(s.factor(D.coeff(u,j))) for j in range(1,M+1)],
            'd1':[str(s.factor(d1.coeff(u,j))) for j in range(1,M+1)]}
        for q in (1,2,3,10):
            exact=counts(M+1,q,'identity' if sign==-1 else 'all')
            for n in range(1,M+2):
                if f[n].subs(u,s.Rational(1,q))*q**(n-1)!=exact[n]:
                    raise ArithmeticError('scaled recurrence failed')
        for n in range(3,M+2):
            expected=sign*s.Rational((n-2)**(n-2),2*s.factorial(n-2))
            if s.diff(f[n],u).subs(u,0)!=expected:
                raise ArithmeticError('first palette coefficient failed')
    alpha,t,k=s.symbols('alpha t k',nonzero=True);lam=a*a/alpha
    P=lam*(t-1)+(a**3*(t**3-t)+2*a**4*t*(1-t))/alpha**2
    reworked=-lam+(lam+(2-1/a)*lam**2)*t-2*lam**2*t*t+lam**2/a*t**3
    if s.expand(P-reworked)!=0 or s.expand(P.subs(t,1))!=0:
        raise ArithmeticError('TV correction identity failed')
    multiplier=sum(s.expand(P).coeff(t,j)*s.ff(k,j)/lam**j for j in range(4))
    expected=-lam+(1+(2-1/a)*lam)*k-2*k*(k-1)+(1/a)/lam*k*(k-1)*(k-2)
    if s.simplify(multiplier-expected)!=0:
        raise ArithmeticError('Poisson multiplier failed')
    return {'status':'pass','palette_order':M,'symbol':'a=exp(-1)','jets':out,'TV_algebra':'exact pass'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=parse_small,default=4)
    print(json.dumps(generate(parser.parse_args().order),indent=2,sort_keys=True))
