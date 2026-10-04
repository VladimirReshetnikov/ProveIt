#!/usr/bin/env python3
"""Reproducible checks for Critical Stokes Reversion and q-Gamma Cores.

Exact algebra uses SymPy. High-precision diagnostics use mpmath; they are
not interval certificates or substitutes for the proofs in critical_stokes_q_reversion.tex.
Run: python verify.py --output results.json
"""
from __future__ import annotations
import argparse, json, math, time
from pathlib import Path
import sympy as sp
import mpmath as mp


def exact_checks() -> dict:
    a, z, h = sp.symbols('a z h')
    count = 0
    # Bernoulli generating-function / Borel-kernel coefficient identity.
    T = sp.sinh((a-sp.Rational(1,2))*z)/(2*sp.sinh(z/2))-(a-sp.Rational(1,2))
    jet = sp.series(T,z,0,14).removeO().expand()
    for k in range(1,7):
        assert sp.simplify(jet.coeff(z,2*k)-sp.bernoulli(2*k+1,a)/sp.factorial(2*k+1)) == 0
        count += 1
    f1=-(a-1)*(a-2)/4
    f2=(2*a**3-3*a**2-5*a+6)/144
    assert sp.expand((1-a)*(-sp.Rational(1,2))+(sp.bernoulli(2,1)-sp.bernoulli(2,a))/4-f1)==0
    assert sp.expand((1-a)/24+sp.bernoulli(2)*sp.bernoulli(3,a)/12-f2)==0
    count += 2
    # Integer q-gamma values give independently finite products.
    for j in range(2,9):
        finite=0
        for k in range(1,j):
            series=sp.series((1-sp.exp(-k*h))/(k*(1-sp.exp(-h))),h,0,7).removeO()
            finite += sp.series(sp.log(series),h,0,7).removeO()
        E=(1-j)*sp.series(sp.log((1-sp.exp(-h))/h),h,0,7).removeO()
        E+=(sp.bernoulli(2,1)-sp.bernoulli(2,j))*h/4
        E+=sum(sp.bernoulli(2*k)*sp.bernoulli(2*k+1,j)*h**(2*k)/(2*k*sp.factorial(2*k+1)) for k in range(1,4))
        assert sp.expand(finite-E)==0
        count += 1
    # Universal second-order inverse response, checked by substitution.
    e, b, c, d, j, k = sp.symbols('e b c d j k')
    u=-d/b
    v=d*j/b**2-c*d*d/(2*b**3)
    w=e*u+e**2*v
    residual=sp.series(b*w+c*w*w/2+e*(d+j*w+k*w*w/2),e,0,3).removeO()
    assert sp.simplify(residual)==0
    count += 1
    # Fold branch coefficients through s^3 for a generic analytic family.
    A,B,C,d0,d1,d2,e0,u0=sp.symbols('A B C d0 d1 d2 e0 u0', nonzero=True)
    s=sp.symbols('s')
    u1=-(B*u0**2+d1)/(2*A)
    u2=-(A*u1**2+3*B*u0**2*u1+C*u0**4+d1*u1+d2*u0**2+e0)/(2*A*u0)
    w=s*u0+s**2*u1+s**3*u2
    residual=sp.series(A*w*w+B*w**3+C*w**4+s**2*(d0+d1*w+d2*w*w)+s**4*e0,s,0,5).removeO()
    assert sp.simplify(residual.coeff(s,3))==0
    assert sp.simplify(residual.coeff(s,4))==0
    count += 2
    # Divisor sums followed by Möbius inversion, exact integer test vectors.
    for N in range(2,16):
        vals={n:sp.Integer(n*n-3*n+7) for n in range(1,N+1)}
        coeff={n:sum(vals[d]/d for d in sp.divisors(n)) for n in vals}
        for n in vals:
            got=n*sum(sp.mobius(n//d)*coeff[d] for d in sp.divisors(n))
            assert got==vals[n]
            count += 1
    # Polynomial-logarithmic h inverse through the displayed orders.
    w, beta, L, r1, r2, A0 = sp.symbols('w beta L r1 r2 A0')
    x=1/w-beta*L+(beta**2*L+r1)*w+(beta**3*L**2/2-beta**3*L+beta*r1*L-beta*r1+r2)*w**2
    logx=L+sp.series(sp.log(w*x),w,0,3).removeO()
    res=sp.series(x+beta*logx-1/w-r1/x-r2/x**2,w,0,3).removeO()
    assert sp.simplify(res)==0
    hjet=A0*w+A0*beta*L*w**2+A0*(beta**2*L**2-beta**2*L-r1)*w**3
    assert sp.simplify(sp.series(A0/x,w,0,4).removeO()-hjet)==0
    count += 2
    # Reflection inverse in z^2, through the Q^3 sector.
    P,h,Q=sp.symbols('P h Q')
    alpha=(P-h)/2
    b1=4/alpha
    b2=(4-P**2*b1**2/12-4*P*b1)/alpha
    b3=(sp.Rational(16,3)-P**2*b1*b2/6-P**3*b1**3/45-4*P*b2+sp.Rational(4,3)*P**2*b1**2+4*P*b1)/alpha
    w=b1*Q+b2*Q**2+b3*Q**3
    polynomial=alpha*w+P**2*w**2/12+P**3*w**3/45+Q*(-4+4*P*w-sp.Rational(4,3)*P**2*w**2)+Q**2*(-4-4*P*w)-sp.Rational(16,3)*Q**3
    res=sp.series(polynomial,Q,0,4).removeO().expand()
    for k in range(1,4):
        assert sp.factor(res.coeff(Q,k))==0
        count += 1
    # Rational bounds used to locate the classical gamma minimum below 3/2.
    log30lower=2*sum(sp.Rational(29,31)**(2*k+1)/sp.Integer(2*k+1) for k in range(100))
    assert sp.harmonic(30)-log30lower<sp.Rational(3,5)
    assert sum(sp.Rational(7,10)**k/sp.factorial(k) for k in range(6))>2
    count += 2
    return {'assertions': count, 'status':'passed'}


def phi_coeff(a: mp.mpf, k: int) -> mp.mpf:
    return mp.bernpoly(2*k+1,a)*mp.bernoulli(2*k)/(2*k*mp.factorial(2*k+1))


def K(T: mp.mpf) -> mp.mpf:
    return (mp.exp(-T)*mp.ei(T)-mp.exp(T)*mp.e1(T))/2


def log_p(a, h):
    q=mp.exp(-h)
    return mp.log(mp.qp(q**a,q))


def core_p(a,h):
    return -mp.pi**2/(6*h)+(mp.mpf('.5')-a)*mp.log(h)+mp.log(2*mp.pi)/2-mp.loggamma(a)+mp.bernpoly(2,a)*h/4


def dual_log(a,Q,sign=1):
    # Entire-in-a local germ, with its unambiguous zero constant term.
    total=mp.mpc(0)
    for m in range(1,10000):
        term=-mp.exp(sign*2j*mp.pi*m*a)*Q**m/(m*(1-Q**m))
        total+=term
        if abs(term)<mp.eps/100:
            return total
    raise RuntimeError('dual series failed to reach requested precision')


def phi_median_accelerated(a,h,cutoff=80,order=10):
    """Actionwise PV with exactly summed subtracted algebraic tails.

    The finite action cutoff is NOT interval-certified. Compare two cutoffs.
    """
    coeff=[phi_coeff(a,k) for k in range(1,order+1)]
    total=sum(coeff[k-1]*h**(2*k) for k in range(1,order+1))
    X=4*mp.pi**2/h
    for n in range(1,cutoff+1):
        sig=sum(mp.sin(2*mp.pi*d*a)/d for d in sp.divisors(n))
        T=X*n
        subtraction=sum(mp.factorial(2*k-1)/T**(2*k) for k in range(1,order+1))
        total+=(2/mp.pi)*sig*(K(T)-subtraction)
    return total


def stokes_checks():
    records=[]
    for astr,hstr in [('0.3','2'),('0.5','2'),('0.7','3')]:
        a,h=mp.mpf(astr),mp.mpf(hstr)
        Q=mp.exp(-4*mp.pi**2/h)
        avg=(dual_log(a,Q,1)+dual_log(a,Q,-1))/2
        value=log_p(a,h)
        p60=phi_median_accelerated(a,h,60,10)
        p120=phi_median_accelerated(a,h,120,10)
        err=abs(value-(core_p(a,h)-p120+avg))
        errcut=abs(p60-p120)
        assert err<mp.mpf('1e-40')
        jump=dual_log(a,Q,-1)-dual_log(a,Q,1)
        js=2j*sum(sum(mp.sin(2*mp.pi*d*a)/d for d in sp.divisors(n))*Q**n for n in range(1,31))
        assert abs(jump-js)<mp.mpf('1e-85')
        records.append({'a':astr,'h':hstr,'Q':mp.nstr(Q,18),'identity_error':mp.nstr(err,8),'cutoff_change_60_to_120':mp.nstr(errcut,8),'jump_series_error':mp.nstr(abs(jump-js),8)})
    return records


def qgamma_functions(h):
    Q=mp.exp(-4*mp.pi**2/h)
    cutoff=int(mp.ceil((mp.mp.dps+15)*mp.log(10)/(mp.mpf('1.3')*h)))
    ms=[mp.mpf(m) for m in range(1,cutoff+1)]
    weights=[1/(1-mp.exp(-h*m)) for m in ms]
    const=mp.log(mp.qp(mp.exp(-h)))
    log1q=mp.log1p(-mp.exp(-h))
    def F(a,der=0):
        if der==0:
            return const+(1-a)*log1q+mp.fsum(mp.exp(-a*h*m)*w/m for m,w in zip(ms,weights))
        ans=(-h)**der*mp.fsum(m**(der-1)*mp.exp(-a*h*m)*w for m,w in zip(ms,weights))
        return ans-log1q if der==1 else ans
    def D(a,der=0):
        ans=mp.mpf(0)
        for m in range(1,200):
            theta=2*mp.pi*m*a
            trig=mp.cos(theta)-1 if der==0 else (2*mp.pi*m)**der*mp.cos(theta+der*mp.pi/2)
            term=trig*Q**m/(m*(1-Q**m))
            ans+=term
            if 2*(2*mp.pi*m)**der*Q**m/(m*(1-Q**m))<mp.eps/100: return ans
        raise RuntimeError('D truncation')
    def H(a,der=0): return F(a,der)-D(a,der)
    return F,D,H,Q


def critical_checks():
    root=mp.findroot(mp.digamma,(mp.mpf('1.4'),mp.mpf('1.5')))
    psi1=mp.polygamma(1,root)
    C=mp.sqrt(2*(1-mp.cos(2*mp.pi*root))/psi1)
    c1=(2*root-3)/(4*psi1)
    records=[]
    for hs in ['2','1','0.5']:
        h=mp.mpf(hs)
        F,D,H,Q=qgamma_functions(h)
        c=mp.findroot(lambda a:H(a,1),(mp.mpf('1.3'),mp.mpf('1.6')))
        cp=mp.findroot(lambda a:F(a,1),c)
        v=H(c)
        curv=H(c,2)/2
        lead=mp.sqrt((1-mp.cos(2*mp.pi*c))/curv)*mp.sqrt(Q)
        # Solve on the normalized scale, not by a poorly conditioned raw step.
        uminus=mp.findroot(lambda u:(F(c+lead*u)-v)/Q,(-mp.mpf('1.1'),-mp.mpf('.9')),tol=mp.mpf('1e-70'))
        uplus=mp.findroot(lambda u:(F(c+lead*u)-v)/Q,(mp.mpf('.9'),mp.mpf('1.1')),tol=mp.mpf('1e-70'))
        err=max(abs(F(c+lead*uminus)-v),abs(F(c+lead*uplus)-v))
        assert err<mp.mpf('1e-85')
        assert abs(uminus+1)<mp.mpf('.01') and abs(uplus-1)<mp.mpf('.01')
        records.append({'h':hs,'Q':mp.nstr(Q,24),'median_critical_point':mp.nstr(c,24),'physical_critical_point':mp.nstr(cp,24),'sqrt_action_displacement':mp.nstr(lead,24),'normalized_lower_root':mp.nstr(uminus,24),'normalized_upper_root':mp.nstr(uplus,24),'critical_value_shift_over_Q':mp.nstr((F(cp)-v)/Q,24),'predicted_value_shift_coefficient':mp.nstr(mp.cos(2*mp.pi*c)-1,24),'root_residual':mp.nstr(err,8)})
    return {'classical_critical_point':mp.nstr(root,50),'limiting_sqrt_action_coefficient':mp.nstr(C,50),'first_algebraic_critical_shift':mp.nstr(c1,40),'rows':records}



def reflection_checks():
    rows=[]
    for hs in ['2','1']:
        h=mp.mpf(hs)
        Q=mp.exp(-4*mp.pi**2/h)
        q=mp.exp(-h)
        def D(a):
            return mp.log(mp.qp(Q))-(dual_log(a,Q,1)+dual_log(a,Q,-1))/2
        def core(a):
            return mp.log(mp.pi/mp.sin(mp.pi*a))+mp.log((1-q)/h)+a*(1-a)*h/2
        aa=mp.mpf('.3')
        physical=mp.log(mp.qgamma(aa,q)*mp.qgamma(1-aa,q))
        identity_error=abs(physical-core(aa)-2*D(aa))
        assert identity_error<mp.mpf('1e-95')
        alpha=(mp.pi**2-h)/2
        beta=mp.pi**4/12
        b1=4/alpha
        b2=(4-beta*b1**2-4*mp.pi**2*b1)/alpha
        lead=mp.sqrt(b1*Q)
        # Use the actual product, not its completion, in the root equation.
        v=core(mp.mpf('.5'))
        def residual(u):
            a=mp.mpf('.5')+lead*u
            return (mp.log(mp.qgamma(a,q)*mp.qgamma(1-a,q))-v)/Q
        u=mp.findroot(residual,(mp.mpf('.9'),mp.mpf('1.1')),tol=mp.mpf('1e-70'))
        ratio=(u-1)/Q
        predicted=b2/(2*b1)
        assert abs(ratio-predicted)<1000*Q
        rows.append({'h':hs,'completion_identity_error':mp.nstr(identity_error,8),'leading_displacement':mp.nstr(lead,24),'normalized_root':mp.nstr(u,30),'first_correction_observed':mp.nstr(ratio,24),'first_correction_predicted':mp.nstr(predicted,24),'normalized_root_residual':mp.nstr(abs(residual(u)),8)})
    return rows

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=Path('results.json'))
    ap.add_argument('--skip-symbolic',action='store_true')
    args=ap.parse_args()
    mp.mp.dps=110
    start=time.time()
    data={'precision_decimal_digits':mp.mp.dps,'numerical_status':'floating-point diagnostics, not interval certification'}
    if not args.skip_symbolic:
        data['exact']=exact_checks()
        print('Exact checks:',data['exact'],flush=True)
    data['summability']=stokes_checks()
    print('Summability checks:',data['summability'],flush=True)
    data['critical']=critical_checks()
    data['reflection']=reflection_checks()
    data['elapsed_seconds']=round(time.time()-start,2)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data['critical'],indent=2),flush=True)
    print('Wrote',args.output,flush=True)

if __name__=='__main__':
    main()
