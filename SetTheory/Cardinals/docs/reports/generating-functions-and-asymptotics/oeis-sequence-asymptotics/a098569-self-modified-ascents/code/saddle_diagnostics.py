#!/usr/bin/env python3
"""Bounded 90-digit diagnostics, without interval-certified asymptotic errors."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
if not hasattr(sys, 'set_int_max_str_digits'):
    raise RuntimeError('Python 3.11 or newer is required')
sys.set_int_max_str_digits(640)
import argparse
import math
import mpmath as mp
from common import REPORT_NUMBER, emit, integer, new_file_path, require
from exact_counts import row, counts, integer_record
from algebra_checks import contraction_terms

PRECISION = 90
MARKS = ('0','-0.25','0.25')


def _phase(n,x,binary=False):
    M=x*(x+1)/2;q=n-x
    if binary:
        return mp.loggamma(M-x+1)-mp.loggamma(q+1)-mp.loggamma(M-n+1)
    return mp.loggamma(M+q)-mp.loggamma(q+1)-mp.loggamma(M)


def _prime(n,x,binary=False):
    M=x*(x+1)/2;q=n-x
    if binary:
        return (x-mp.mpf('.5'))*mp.digamma(M-x+1)+mp.digamma(q+1)-(x+mp.mpf('.5'))*mp.digamma(M-n+1)
    return (x-mp.mpf('.5'))*mp.digamma(M+q)+mp.digamma(q+1)-(x+mp.mpf('.5'))*mp.digamma(M)


def _root(fun,a,b):
    """Bisection at finite precision; a residual check is not an interval proof."""
    fa=fun(a);fb=fun(b)
    require(mp.isfinite(fa) and mp.isfinite(fb) and fa*fb<0,'root must have finite opposite endpoint signs')
    for unused in range(300):
        x=(a+b)/2;fx=fun(x)
        require(mp.isfinite(fx),'nonfinite root value')
        if abs(fx)<mp.mpf('1e-78'):
            return x
        if fa*fx>0:a=x;fa=fx
        else:b=x;fb=fx
    x=(a+b)/2
    require(abs(fun(x))<mp.mpf('1e-72'),'bounded root iteration residual')
    return x


def _saddle(n,t,binary=False):
    L=mp.log(n)
    a=max(mp.mpf(1),n/(2*L));b=min(n-mp.mpf('.01'),4*n/L)
    if binary:a=max(a,(-1+mp.sqrt(1+8*n))/2+mp.mpf('.01'))
    r=_root(lambda x:_prime(n,x,binary)+t,a,b)
    require(a<r<b,'computed saddle outside checked bracket')
    return r


def saddle(n,mark='0',binary=False):
    integer(n,100,2000,'diagnostic size')
    require(isinstance(mark,str) and mark in MARKS,'mark must be 0 or +/-0.25')
    require(isinstance(binary,bool),'binary flag must be bool')
    with mp.workdps(PRECISION):
        return _saddle(mp.mpf(n),mp.mpf(mark),binary)


def _contraction(order,lambdas,etas=None):
    values=lambdas+(etas if etas is not None else [])
    total=mp.mpf(0)
    for coefficient,powers in contraction_terms(order,etas is not None):
        term=mp.mpf(int(coefficient.p))/int(coefficient.q)
        for value,power in zip(values,powers):term*=value**power
        total+=term
    return total


def _txt(value):return mp.nstr(value,30)


def _log_carrier(y,order):
    r=_saddle(y,mp.mpf(0))
    d={j:mp.diff(lambda x:_phase(y,x),r,j) for j in range(2,9)}
    A=-d[2]
    require(A>0,'inverse carrier curvature')
    lambdas=[d[j]/A**(mp.mpf(j)/2) for j in range(3,9)]
    correction=mp.fsum(_contraction(k,lambdas) for k in range(order))
    require(correction>0,'inverse carrier correction must be positive')
    return _phase(y,r)+mp.log(2*mp.pi/A)/2+mp.log(correction)


def inverse_diagnostic():
    """One bounded smooth-carrier inversion at an exact integer threshold."""
    with mp.workdps(PRECISION):
        b=counts(1000)[0];target=mp.log(b)
        a=mp.mpf('999.99');z=mp.mpf('1000.01')
        fa=_log_carrier(a,2)-target;fz=_log_carrier(z,2)-target
        require(fa<0<fz,'inverse diagnostic endpoint signs')
        for iteration in range(20):
            x=(a*fz-z*fa)/(fz-fa)
            require(a<x<z,'inverse secant must remain in sign bracket')
            fx=_log_carrier(x,2)-target
            if abs(fx)<mp.mpf('1e-40'):break
            if fx<0:a=x;fa=fx
            else:z=x;fz=fx
        else:raise RuntimeError('inverse diagnostic iteration cutoff')
        require(counts(999)[0]<b,'exact threshold predecessor')
        return {'target':'X=b_1000 (exact integer)', 'actual_integer_threshold':1000,'K':2,
                'smooth_carrier_root_estimate':_txt(x),'root_estimate_minus_1000':_txt(x-1000),
                'finite_precision_log_residual':_txt(fx),'secant_iterations':iteration+1,
                'method':'finite-precision sign-bracketed secant, maximum 20 steps',
                'scope':'Numerical estimate only; sign evaluations are not interval-certified and no asymptotic error constant is supplied'}


def run_case(n,mark='0'):
    integer(n,100,2000,'diagnostic size')
    require(isinstance(mark,str) and mark in MARKS,'mark must be 0 or +/-0.25')
    with mp.workdps(PRECISION):
        t=mp.mpf(mark);r=_saddle(mp.mpf(n),t)
        derivatives={j:mp.diff(lambda x:_phase(n,x),r,j) for j in range(2,9)}
        A=-derivatives[2];require(A>0,'positive ordinary curvature')
        lambdas=[derivatives[j]/A**(mp.mpf(j)/2) for j in range(3,9)]
        C=[mp.mpf(1)]+[_contraction(k,lambdas) for k in (1,2,3)]
        weights=row(n);binary_weights=row(n,True)
        weighted=[mp.mpf(v)*mp.exp(t*m) for m,v in enumerate(weights,1)]
        total=mp.fsum(weighted)
        mean=mp.fsum(m*v for m,v in enumerate(weighted,1))/total
        var=mp.fsum((m-mean)**2*v for m,v in enumerate(weighted,1))/total
        log_carrier=_phase(n,r)+t*r+mp.log(2*mp.pi/A)/2
        relative=mp.exp(mp.log(total)-log_carrier)
        mean_approx=r+derivatives[3]/(2*A**2)
        var_approx=1/A+derivatives[4]/(2*A**3)+derivatives[3]**2/A**4
        L=mp.log(n)
        outside=mp.fsum(v for m,v in enumerate(weighted,1) if m<n/(2*L) or m>4*n/L)
        llterr=max(abs(v/total/mp.sqrt(A)-mp.exp(-A*(m-r)**2/2)/mp.sqrt(2*mp.pi)) for m,v in enumerate(weighted,1))
        result={'N':n,'mark_t':mark,'r':_txt(r),'A':_txt(A),'exact_finite_sum_log':_txt(mp.log(total)),
                'mean':_txt(mean),'variance':_txt(var),'N_C1':_txt(n*C[1]),'N2_C2':_txt(n*n*C[2]),'N3_C3':_txt(n**3*C[3]),
                'relative_residuals':{str(k):_txt(relative-mp.fsum(C[:k])) for k in range(1,5)},
                'residual_key':'k means exact_sum/untruncated_gamma_carrier minus C_0 through C_(k-1)',
                'mean_error_times_N_logN':_txt((mean-mean_approx)*n*L),
                'variance_error_times_N2_A':_txt((var-var_approx)*n*n*A),
                'tail_outside_dominant_interval':_txt(outside/total),'full_support_LLT_sup_error':_txt(llterr),
                'saddle_residual':_txt(_prime(n,r)+t)}
        if t!=0:return result
        b=sum(weights);c=sum(binary_weights);probability=mp.mpf(c)/b
        h=lambda x:_phase(n,x,True)-_phase(n,x)
        hr=h(r);hd=[mp.diff(h,r,j) for j in range(1,7)]
        eta=[v/A**(mp.mpf(j)/2) for j,v in enumerate(hd,1)]
        G1=_contraction(1,lambdas,eta);G2=_contraction(2,lambdas,eta)
        Q1=G1-C[1];Q2=G2-C[1]*Q1-C[2]
        excess=probability*mp.exp(-hr)-1
        u=_root(lambda z:z+mp.log(z)+mp.log(z+2)-mp.log(2*n),mp.mpf('.01'),mp.log(2*n))
        P=u*u+4*u+2
        R=u*(u+2)*(u**4+8*u**3+22*u**2+20*u+8)/(4*P**2)
        leading=n*u*(u+1)/(u+2)
        elementary_plus=leading+u/2+u*u/4+mp.log(2/P)/2
        elementary_minus=leading-u/2-u*u/4+mp.log(2/P)/2
        binary_r=_saddle(mp.mpf(n),mp.mpf(0),True)
        binary_A=-mp.diff(lambda x:_phase(n,x,True),binary_r,2)
        require(binary_A>0,'positive binary curvature')
        m=int(mp.nint(r));M=m*(m+1)//2;q=n-m
        require(q<=M-m,'central dimension must be binary feasible')
        ratio=mp.mpf(binary_weights[m-1])/weights[m-1]
        require(abs(mp.exp(h(m))/ratio-1)<mp.mpf('1e-75'),'gamma conditional product agrees with exact rational count')
        LX=mp.log(b)
        v=_root(lambda z:z+2*mp.log(z)+mp.log(z+1)-mp.log(2*LX),mp.mpf('.01'),mp.log(2*LX))
        n0=LX*(v+2)/(v*(v+1))
        seed=n0-v/4-mp.mpf('.5')+mp.log((v*v+4*v+2)/2)/(2*v)
        LXc=mp.log(c)
        vc=_root(lambda z:z+2*mp.log(z)+mp.log(z+1)-mp.log(2*LXc),mp.mpf('.01'),mp.log(2*LXc))
        n0c=LXc*(vc+2)/(vc*(vc+1))
        seedc=n0c+vc/4+mp.mpf('.5')+mp.log((vc*vc+4*vc+2)/2)/(2*vc)
        if n==1000:
            require(counts(999)[0]<b and int(mp.ceil(seed))==1001,'elementary inverse rounding counterexample')
            result['rounding_warning']={'target':'X=b_1000','actual_threshold':1000,'ceiling_of_elementary_seed':1001,
                                        'conclusion':'Rounding the elementary seed is incorrect at this exact threshold'}
        result.update({'b_N':integer_record(b),'c_N':integer_record(c),'probability':_txt(probability),
                       'binary_saddle':_txt(binary_r),'binary_saddle_shift':_txt(binary_r-r),
                       'binary_shift_prediction':_txt(hd[0]/A),'Q1':_txt(Q1),'Q2':_txt(Q2),
                       'h_at_denominator_saddle':_txt(hr),
                       'exact_h_relative_excess':_txt(excess),'exact_h_error_after_Q1':_txt(excess-Q1),
                       'exact_h_error_after_Q1_Q2':_txt(excess-Q1-Q2),'implicit_u':_txt(u),
                       'u_relative_excess':_txt(probability*mp.exp(u*u/2+u)-1),'R_u_over_N':_txt(R/n),
                       'u_corrected_error':_txt(probability*mp.exp(u*u/2+u)-1-R/n),
                       'ordinary_elementary_log_error':_txt(mp.log(b)-elementary_plus),
                       'binary_elementary_log_error':_txt(mp.log(c)-elementary_minus),
                       'ordinary_inverse_seed_at_b_N':_txt(seed),'ordinary_inverse_seed_error':_txt(seed-n),
                       'binary_inverse_seed_at_c_N':_txt(seedc),'binary_inverse_seed_error':_txt(seedc-n)})
        return result


def verify(max_n=2000):
    integer(max_n,100,2000,'maximum diagnostic size')
    cases=[run_case(n) for n in (100,200,500,1000,2000) if n<=max_n]
    cases += [run_case(min(500,max_n),mark) for mark in ('-0.25','0.25')]
    return {'status':'PASS finite consistency checks','report_number':REPORT_NUMBER,
            'scope':'High-precision numerical diagnostics; no interval certificate, asymptotic proof, finite-N error guarantee, or exact-ceiling claim',
            'precision_decimal_digits':PRECISION,'displayed_significant_digits':30,'mpmath_version':mp.__version__,
            'root_method':'finite-precision bisection, opposite endpoint signs and residual checked, at most 300 steps',
            'cases':cases,'exact_carrier_inverse_diagnostic':inverse_diagnostic() if max_n>=1000 else None}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--max-n',type=int,default=2000);parser.add_argument('--output')
    args=parser.parse_args();integer(args.max_n,100,2000,'maximum diagnostic size')
    if args.output is not None:new_file_path(args.output)
    emit(verify(args.max_n),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
