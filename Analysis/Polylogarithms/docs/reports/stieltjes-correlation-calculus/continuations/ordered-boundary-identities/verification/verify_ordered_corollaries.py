#!/usr/bin/env python3
"""Independent checks of the digamma master and the cutoff subtraction."""
from pathlib import Path
from math import comb, factorial
import json
import sympy as sp
import mpmath as mp
from verify_ordered_boundary import original_partial


def sign(k):
    return 1 if k % 2 == 0 else -1


def unit_ordered_closed(p,q):
    N=p+q
    result=(1-sp.Rational(1,2**p))/2*(sp.zeta(q)-1)
    for j in range(2,max(p,q)+1):
        L=comb(N-j-1,q-1) if j<=p else 0
        R=comb(N-j-1,p-1) if j<=q else 0
        result+=sp.Rational(sign(q),4)*(1-sign(N-j))*(L+sign(j)*R)*(sp.zeta(j)-1)
    for k in range(1,p+1):
        result-=sp.Rational(1,4)*comb(N-k-1,q-1)*(sign(q)*sp.Rational(1,2**k)+sign(p-k))
    return result


def exact_F_derivatives():
    a,b=sp.symbols('a b', positive=True)
    y=b+1
    DD=lambda x:(sp.polygamma(0,y)-sp.polygamma(0,x))/(y-x)
    F=-sp.polygamma(0,y)/(2*a*(a+1))+(DD(a+2)-DD(a))/4
    checks=0
    for p in range(1,5):
        for q in range(2,5):
            lhs=sign(p+q-2)*sp.diff(F,a,p-1,b,q-1).subs({a:1,b:1})/(factorial(p-1)*factorial(q-1))
            assert sp.simplify(sp.expand_func(lhs)-unit_ordered_closed(p,q))==0
            checks+=1
    assert sp.simplify(F.subs({a:1,b:1})-(sp.EulerGamma/4-sp.Rational(3,8)))==0
    return checks+1


def stieltjes_coefficients():
    e=sp.symbols('e')
    g=sp.symbols('g0:9')
    zeta=1/e+sum(sign(j)*g[j]*e**j/sp.factorial(j) for j in range(9))
    product=sp.expand((-3*e-e**2)*zeta/2)
    for m in range(9):
        actual=sp.expand(product).coeff(e,m)*factorial(m)
        if m==0:
            expected=-sp.Rational(3,2)
        elif m==1:
            expected=-(1+3*g[0])/2
        else:
            expected=sign(m)*(sp.Rational(3*m,2)*g[m-1]-sp.Rational(m*(m-1),2)*g[m-2])
        assert sp.simplify(actual-expected)==0
    return 9


def mp_F(a,b):
    y=b+1
    def DD(x):
        return mp.polygamma(1,x) if x==y else (mp.digamma(y)-mp.digamma(x))/(y-x)
    return -mp.digamma(y)/(2*a*(a+1))+(DD(a+2)-DD(a))/4


def geometric_master():
    a,b,x,y=map(mp.mpf,['1','1','0.2','0.3'])
    A,B=a-x,b-y
    N=4000
    M=[mp.mpf(0),mp.mpf(0),mp.mpf(0)]
    partial=mp.mpf(0)
    def w1(n,z):
        # Exact rational factorization of half the second difference.
        return 1/((n+z)*(n+z+1)*(n+z+2))
    for n in range(N+1):
        inner=n*n*M[0]-2*n*M[1]+M[2]
        partial+=(w1(n,B)-w1(n,b))*inner
        wf=w1(n,A)
        for j in range(3):
            M[j]+=n**j*wf
    value=mp_F(A,B)-mp_F(A,b)
    EA=1/(2*A*(A+1))
    bound=3*y*EA*mp.zeta(2,N+B+1)
    assert 0<value-partial<bound
    return dict(a=str(a),b=str(b),x=str(x),y=str(y),N=N,
                value=mp.nstr(value,40),original_partial=mp.nstr(partial,40),
                discrepancy=mp.nstr(value-partial,12),
                analytic_positive_tail_envelope=mp.nstr(bound,12))


def U0_and_cutoff():
    rows=[]
    for s in (2,3):
        E=(1-mp.mpf(2)**(-s))/2
        def inner(n):
            return (n*n+(-n*n-2*n+1)*mp.mpf(2)**(-s)
                    +2*(mp.zeta(s,3)-mp.zeta(s,n+2))+(n+2)**(-s))/2
        def summand(n):
            return inner(n)/((n+1)*(n+2)*(n+3))-E/(n+1)
        numerical=mp.nsum(summand,[1,mp.inf],method='richardson',maxterms=2000)
        closed=mp.mpf(1)/8-mp.zeta(2)/2 if s==2 else -mp.mpf(3)/16-mp.zeta(3)/2
        error=abs(numerical-closed)
        assert error<mp.mpf('1e-45')
        constant=closed+E*(mp.euler-1)
        cutoffs=[]
        for N in (1000,2000,4000):
            actual=original_partial(s,1,1,1,N)-E*mp.log(N+1)
            cutoffs.append(dict(N=N,value=mp.nstr(actual,30),
                                discrepancy=mp.nstr(actual-constant,12)))
        assert abs(mp.mpf(cutoffs[-1]['discrepancy']))<mp.mpf('0.002')
        rows.append(dict(s=s,U0=mp.nstr(closed,45),
                         original_subtracted_sum=mp.nstr(numerical,45),
                         absolute_error=mp.nstr(error,12),
                         cutoff_constant=mp.nstr(constant,45),
                         cutoff_diagnostics=cutoffs))
    return rows


def arcsine_checks():
    rows=[]
    for a in map(mp.mpf,['0.4','1','2.5']):
        def integral(f):
            return 2*mp.quad(lambda theta:f(mp.sin(theta)**2),[0,mp.pi/2])
        digamma=integral(lambda u:mp.digamma(a+1+u)-mp.digamma(a+1-u))
        dclosed=mp.pi/mp.sqrt(a*(a+1))
        gamma=integral(lambda u:mp.loggamma(a+1+u)-mp.loggamma(a+1-u))
        gclosed=2*mp.pi*mp.log((mp.sqrt(a)+mp.sqrt(a+1))/2)
        logarithmic=integral(lambda u:mp.log(a+u)/(a+u))
        lclosed=mp.pi/mp.sqrt(a*(a+1))*mp.log(4*a*(a+1)/(mp.sqrt(a)+mp.sqrt(a+1))**2)
        errors=[abs(digamma-dclosed),abs(gamma-gclosed),abs(logarithmic-lclosed)]
        assert max(errors)<mp.mpf('1e-45')
        rows.append(dict(a=str(a),digamma_error=mp.nstr(errors[0],12),
                         gamma_error=mp.nstr(errors[1],12),
                         logarithmic_error=mp.nstr(errors[2],12)))
    return rows


def main():
    mp.mp.dps=55
    report=dict(exact_digamma_master_derivatives=exact_F_derivatives(),
                exact_stieltjes_jet_coefficients=stieltjes_coefficients(),
                geometric_master_original_series=geometric_master(),
                subtracted_original_series=U0_and_cutoff(),
                arcsine_quadratures=arcsine_checks(),
                interpretation=('Exact checks concern symbolic identities. '
                                'Numerical sums and quadratures are diagnostics, '
                                'not interval-certified proofs.'))
    out=Path(__file__).with_name('ordered_corollary_checks.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
