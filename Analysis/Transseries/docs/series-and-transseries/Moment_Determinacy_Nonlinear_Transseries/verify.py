#!/usr/bin/env python3
"""Reproduce finite checks for Moment Determinacy and Nonlinear Transseries.

These are arbitrary-precision consistency tests, not interval proofs. All
infinite identities and error estimates are proved in the accompanying paper.
No network access is used.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
from typing import Callable
import mpmath as mp


def text(x: mp.mpf, digits: int = 24) -> str:
    return mp.nstr(x, digits)


def assert_close(a: mp.mpf, b: mp.mpf, tol: mp.mpf, label: str) -> mp.mpf:
    error = abs(a - b) / max(abs(b), mp.mpf('1e-90'))
    if error > tol:
        raise AssertionError(f'{label}: relative error {error}')
    return error


def inverse(S: Callable, Sp: Callable, y: mp.mpf) -> mp.mpf:
    """Newton iteration for t=y S(t), starting in its small positive branch."""
    t = y
    for _ in range(60):
        step = (t-y*S(t))/(1-y*Sp(t))
        tnew = t-step
        if tnew <= 0:
            tnew = t/2
        if abs(tnew-t) < mp.eps*100*max(abs(tnew), mp.mpf('1e-100')):
            return tnew
        t = tnew
    raise RuntimeError('Newton iteration did not converge')


class QFamily:
    def __init__(self, q: mp.mpf):
        if not 0 < q < 1:
            raise ValueError('q must lie in (0,1)')
        self.q = q
        self.h = -mp.log(q)
        self.cut = int(mp.ceil(mp.sqrt(2*(mp.mp.dps+45)*mp.log(10)/self.h)))+12
        self.terms = [(n, q**(mp.mpf(n)*(n-1)/2), q**(-n))
                      for n in range(-self.cut, self.cut+1)]
        self.M = mp.fsum(w for n,w,_ in self.terms if n % 2 == 0)
        self.K = mp.qp(q,q)**3/self.M

    def S(self, t, parity=1, derivative=0):
        return ((-1)**derivative*mp.factorial(derivative)/self.M
                *mp.fsum(w*lam**derivative/(1+t*lam)**(derivative+1)
                         for n,w,lam in self.terms if n % 2 == parity))

    def P(self, x, derivative=0):
        frac=x-mp.floor(x)
        if derivative==0:
            return mp.fsum(mp.exp(-self.h*(n+frac)**2/2)
                           for n in range(-self.cut,self.cut+1))
        if derivative==1:
            return mp.fsum(-self.h*(n+frac)*mp.exp(-self.h*(n+frac)**2/2)
                           for n in range(-self.cut,self.cut+1))
        raise ValueError('only derivatives zero and one are implemented')

    def D(self,t):
        x=-mp.log(t)/self.h
        return self.K*mp.exp(-self.h*(x-mp.mpf('.5'))**2/2)/self.P(x-mp.mpf('.5'))

    def Dproduct(self,t):
        return mp.qp(self.q,self.q)**2/(self.M*mp.qp(-t,self.q)*mp.qp(-self.q/t,self.q))

    def alpha_phase(self,x):
        return -mp.mpf('.5')+self.P(x-mp.mpf('.5'),1)/(self.h*self.P(x-mp.mpf('.5')))

    def Dprime(self,t):
        x=-mp.log(t)/self.h
        return self.D(t)*(x+self.alpha_phase(x))/t


class GammaCubic:
    """alpha=beta=1/3; m_n=(3n)! and D=pi/3 t^(-1/3)e^(-2t^(-1/3))."""
    def __init__(self):
        self.alpha=mp.mpf(1)/3
        self.beta=self.alpha
        self.A=mp.mpf(2)

    def S(self,t,derivative=0):
        fac=(-1)**derivative*mp.factorial(derivative)
        return fac*mp.quad(lambda u:mp.exp(-u)*u**(3*derivative)/(1+t*u**3)**(derivative+1),
                           [0,1,4,12,40,mp.inf])

    def D(self,t):
        return mp.pi/3*t**(-self.beta)*mp.exp(-2*t**(-self.alpha))

    def Dprime(self,t):
        return self.D(t)*(2*self.alpha*t**(-self.alpha)-self.beta)/t


def integer_inverse_coefficients(order: int):
    """Exact coefficient formula using integer polynomial convolution."""
    moments=[math.factorial(3*k) for k in range(order)]
    ans=[]
    for n in range(1,order+1):
        poly=[1]+[0]*(n-1)
        for _ in range(n):
            new=[0]*n
            for i,a in enumerate(poly):
                for j in range(n-i):
                    new[i+j] += a*moments[j]
            poly=new
        assert poly[n-1] % n == 0
        ans.append((-1)**(n-1)*(poly[n-1]//n))
    # Independently verify T = y sum (-1)^k (3k)! T^k.
    T=[0]+ans
    powers=[[1]+[0]*order]
    for k in range(1,order):
        prev=powers[-1]; curr=[0]*(order+1)
        for i,a in enumerate(prev):
            for j in range(1,order+1-i):
                curr[i+j]+=a*T[j]
        powers.append(curr)
    rhs=[0]*(order+1)
    for k in range(order):
        for j in range(order):
            rhs[j+1]+=(-1)**k*moments[k]*powers[k][j]
    assert rhs==T
    return ans


def run() -> dict:
    results={'environment':{'python':platform.python_version(),'mpmath':mp.__version__,
                            'decimal_precision':mp.mp.dps},
             'qualification':'Finite non-interval consistency tests; not formal verification.'}
    results['cubic_inverse_coefficients']=integer_inverse_coefficients(12)
    qf=QFamily(mp.mpf('.5'))
    errors=[]
    for k in range(13):
        target=qf.q**(-mp.mpf(k)*(k+1)/2)
        for parity in (0,1):
            val=mp.fsum(w*lam**k for n,w,lam in qf.terms if n%2==parity)/qf.M
            errors.append(assert_close(val,target,mp.mpf('1e-75'),'q moments'))
    results['q_moment_max_relative_error']=text(max(errors))

    # A different, full shifted-lattice family satisfies the exact FIRST-order
    # q-Euler equation; it must not be confused with the parity family above.
    def shifted_data(r):
        terms=[(w*r**(-n),r*lam) for n,w,lam in qf.terms]
        z=mp.fsum(a for a,_ in terms)
        return [(a/z,lam) for a,lam in terms]
    shifted={"one":shifted_data(mp.mpf(1)),
             "sqrt_q":shifted_data(mp.sqrt(qf.q))}
    def Us(t,key):
        return mp.fsum(a/(1+t*lam) for a,lam in shifted[key])
    se=[]
    for key,terms in shifted.items():
        for k in range(9):
            target=qf.q**(-mp.mpf(k)*(k+1)/2)
            se.append(assert_close(mp.fsum(a*lam**k for a,lam in terms),target,
                                   mp.mpf('1e-75'),'shifted moments'))
        for t in (mp.mpf('.07'),mp.mpf('.2'),mp.mpf('1.3')):
            se.append(assert_close(Us(qf.q*t,key),1-t*Us(t,key),
                                   mp.mpf('1e-75'),'exact first-order q Euler'))
    alternating=[]
    t=mp.mpf('.07')
    last=None
    for n in range(4):
        tn=t*qf.q**n
        value=Us(tn,'sqrt_q')-Us(tn,'one')
        if last is not None:
            assert value*last<0
            assert_close(value,-(tn/qf.q)*last,mp.mpf('1e-70'),
                         'alternating homogeneous q equation')
        alternating.append(text(value))
        last=value
    results['shifted_q_first_order_check']={
        'max_scaled_error':text(max(se)),
        'difference_at_0_07_times_q_to_n':alternating}
    qtable=[]
    for exponent in (4,8,12,20):
        t=qf.q**exponent
        direct=qf.S(t,0)-qf.S(t,1)
        d=qf.D(t)
        assert_close(direct,d,mp.mpf('1e-55'),'theta gap')
        assert_close(qf.Dproduct(t),d,mp.mpf('1e-75'),'product versus Gaussian theta')
        assert_close(qf.D(qf.q*t),t*d,mp.mpf('1e-75'),'q scaling')
        for parity in (0,1):
            assert_close(qf.S(qf.q**2*t,parity),1-qf.q*t+qf.q*t*t*qf.S(t,parity),
                         mp.mpf('1e-75'),'q squared equation')
        tm=inverse(lambda z:qf.S(z,1),lambda z:qf.S(z,1,1),t)
        tp=inverse(lambda z:qf.S(z,0),lambda z:qf.S(z,0,1),t)
        ratio=(tp-tm)/(t*d)
        x=mp.mpf(exponent)
        corrected=1-t/qf.q*(x+qf.alpha_phase(x)+1)
        n=int(mp.nint(x-mp.mpf('.5')))
        optimum=t**n*qf.q**(-mp.mpf(n)*(n+1)/2)
        qtable.append({'y':text(t),'D_y':text(d),'inverse_gap_ratio':text(ratio),
                       'first_corrected_ratio':text(corrected),
                       'D_over_least_moment_bound':text(d/optimum)})
    results['q_table']=qtable

    gf=GammaCubic()
    gtable=[]
    for t in (mp.mpf('1'),mp.mpf('.1'),mp.mpf('.01')):
        signed=mp.quad(lambda u:mp.exp(-u)*mp.sin(mp.sqrt(3)*u-mp.pi/3)/(1+t*u**3),
                       [0,1,4,12,40,mp.inf])
        err=assert_close(signed,-gf.D(t),mp.mpf('1e-45'),'gamma exact defect')
        gtable.append({'t':text(t),'signed_transform':text(signed),'closed_form':text(-gf.D(t)),
                       'relative_error':text(err)})
    results['gamma_integral_table']=gtable
    gi=[]
    for y in (mp.mpf('.001'),mp.mpf('.0001')):
        t0=inverse(lambda z:gf.S(z),lambda z:gf.S(z,1),y)
        t1=inverse(lambda z:gf.S(z)+gf.D(z),lambda z:gf.S(z,1)+gf.Dprime(z),y)
        ratio=(t1-t0)/(y*gf.D(y))
        corr=1-4*y**(mp.mpf(2)/3)-4*y
        gi.append({'y':text(y),'gap_ratio':text(ratio),'first_corrected_ratio':text(corr),
                   'scaled_correction_error':text((ratio-corr)/y**(mp.mpf(4)/3))})
    results['gamma_inverse_table']=gi

    # Stable fold evaluation: subtract S(t)-S(t0) inside the sum, not two O(1) quantities.
    folds=[]
    for exponent in (12,20,32):
        t0=qf.q**exponent
        y=t0/qf.S(t0,1)
        p=mp.mpf(exponent)
        d0=qf.D(t0)
        def H(t):
            diff=(t0-t)*mp.fsum(w*lam/((1+t*lam)*(1+t0*lam))
                                for n,w,lam in qf.terms if n%2==1)/qf.M
            return (t-t0)-y*diff
        def equation(v):
            t=t0*(1+v/p)
            return (1-y*qf.S(t,1,1))*qf.D(t)-H(t)*qf.Dprime(t)
        vc=mp.findroot(equation,(mp.mpf('.85'),mp.mpf('1.3')),verify=False)
        tc=t0*(1+vc/p)
        kc=p*H(tc)/t0*d0/qf.D(tc)
        a=qf.alpha_phase(p)
        vpred=1+(1-a)/p
        kpred=(1+(mp.mpf('.5')-a)/p)/mp.e
        if not mp.mpf('.8') < vc < mp.mpf('1.5'):
            raise AssertionError('fold root outside local branch')
        assert abs(equation(vc)) < abs(d0)*mp.mpf('1e-50')
        folds.append({'p':exponent,'v_critical':text(vc),'v_first_correction':text(vpred),
                      'kappa_critical':text(kc),'kappa_first_correction':text(kpred),
                      'p2_v_error':text(p*p*(vc-vpred)),
                      'p2_kappa_error':text(p*p*(kc-kpred))})
    results['q_fold_table']=folds

    # Exact low-order Lagrange formulas, cross-checked by direct implicit derivatives.
    y=qf.q**8
    t0=inverse(lambda z:qf.S(z,1),lambda z:qf.S(z,1,1),y)
    d=qf.D(t0); dp=qf.Dprime(t0); B=1-y*qf.S(t0,1,1)
    a1=y*d/B
    a2=y*y*d*dp/(B*B)+y**3*d*d*qf.S(t0,1,2)/(2*B**3)
    # Bound from the Cauchy-disc theorem and direct second-sector comparison.
    x=-mp.log(t0)/qf.h
    r=t0/(8*(x+4/(1-qf.q)))
    M=2*mp.exp(mp.mpf('.25'))*y*d
    rho=M/r
    t1=inverse(lambda z:qf.S(z,0),lambda z:qf.S(z,0,1),y)
    remainder=abs(t1-t0-a1-a2)
    bound=r*rho**3/(3*(1-rho))
    assert remainder<=bound
    results['two_sector_check']={'a1':text(a1),'a2':text(a2),'actual_remainder':text(remainder),
                                  'proved_bound_evaluated':text(bound),'rho':text(rho)}
    results['status']='all assertions passed'
    return results


def main() -> None:
    parser=argparse.ArgumentParser()
    # Editorial amendment (ProveIt, 2026-09-29): without --output, a run at a
    # precision other than the recorded 130 digits writes
    # verification_results_dps<N>.json instead of overwriting the recorded file.
    parser.add_argument('--output',type=Path,default=None)
    parser.add_argument('--dps',type=int,default=130)
    args=parser.parse_args()
    if args.dps<115:
        parser.error('at least 115 digits are required for cancellation-sensitive gap tests')
    if args.output is None:
        args.output=Path('verification_results.json' if args.dps==130
                         else f'verification_results_dps{args.dps}.json')
    mp.mp.dps=args.dps
    data=run()
    args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':
    main()
