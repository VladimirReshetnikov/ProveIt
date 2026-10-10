"""Exact transition and inverse polynomials; no numerical fitting."""
from pathlib import Path
import json
import sympy as s

L,v,a,t,e=s.symbols('L v a t e')

def D(poly):
    return s.expand(v*poly-v*s.diff(poly,v))

def dj(j,poly):
    # (-1)^j/(j+1) [a^(j+1)-(a-D)^(j+1)]
    result=0
    power=poly
    for k in range(1,j+2):
        power=D(power)
        result += (-1)**(j+k+1)*s.binomial(j+1,k)*a**(j+1-k)*power/s.Integer(j+1)
    return s.expand(result)

def forward(order):
    ell=s.series(s.log(s.log(1+t)/t),t,0,order+2).removeO().expand()
    coeff={k:s.expand(2**(k+1)*ell.coeff(t,k+1)*v**(k+1)+(-1)**k*2**k*v**k/s.Integer(k)) for k in range(1,order+1)}
    U=[s.Integer(1)]
    for n in range(1,order+1):
        U.append(s.expand(sum(k*coeff[k]*U[n-k] for k in range(1,n+1))/n))
    cache={}
    def op(n,m):
        if n==0:return U[m]
        if (n,m) not in cache:
            cache[n,m]=s.expand(L*sum(k*dj(k,op(n-k,m)) for k in range(1,n+1))/n)
        return cache[n,m]
    theta=[s.expand(sum(op(n-m,m) for m in range(n+1))) for n in range(order+1)]
    return U,theta

def inverse_first_two(theta):
    f1,f2=theta[1],theta[2]
    q0=s.cancel(-f1/v).expand()
    q1=s.cancel(q0*q0/2-(q0*(s.diff(f1,L)-v*s.diff(f1,v))+f2-f1*f1/2)/v).expand()
    return [q0,q1]

def verify(theta,Q):
    expected1=(v*v/2-(a+s.Rational(1,2))*v)*L+s.Rational(5,6)*v*v-2*v
    assert s.expand(theta[1]-expected1)==0
    q0,q1=Q
    # Coefficients of the original non-logarithmic composition, with
    # monomial binomial substitution (avoid expanding irrelevant orders).
    drift=0
    for (i,j,k),c in s.Poly(theta[1],L,v,a).terms():
        drift += c*v**j*a**k*((i*L**(i-1) if i else 0)-j*L**i)
    c1=v*q0+theta[1]
    c2=v*q1+(v*v-v)*q0*q0/2+q0*drift+theta[2]+v*q0*theta[1]
    assert s.expand(c1)==0
    assert s.expand(c2)==0
    for j,q in enumerate(Q):
        assert s.Poly(q,L).degree()<=j+1
        assert s.denom(q)==1
    return {'forward_first_coefficient':True,'inverse_coefficients':[1,2],'all_checks_passed':True}

def main():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('inverse_polynomials.json'))
    args=parser.parse_args()
    U,theta=forward(3)
    Q=inverse_first_two(theta)
    checks=verify(theta,Q)
    data={'kind':'exact symbolic identities','symbols':{'L':'log(h)-log(2 lambda)','v':'lambda=-log(theta)','a':'shift'},'U':[str(x) for x in U],'Theta':[str(x) for x in theta],'Q':[str(x) for x in Q],'Q_latex':[s.latex(s.collect(x,L)) for x in Q],'verification':checks}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'Q':[str(s.collect(x,L)) for x in Q],'verification':checks},indent=2))

if __name__=='__main__':main()
