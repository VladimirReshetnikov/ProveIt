"""Independent floating-point audits of fully shifted height-one identities.

A Gamma-ratio asymptotic tail evaluates the defining Dirichlet series after
meromorphic continuation. This differs from the hypergeometric-Mellin proof.
The asymptotic tail is truncated, so the checks are not interval certificates.
"""
from __future__ import annotations
import json
import time
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 75
HERE = Path(__file__).resolve().parent


def gamma_ratio_coeffs(u, order):
    log_coeff = [mp.mpf(0)] + [(-1)**(k+1)*(mp.bernpoly(k+1,u)-mp.bernoulli(k+1))/(k*(k+1)) for k in range(1,order)]
    coeff = [mp.mpf(1)]
    for k in range(1, order):
        coeff.append(mp.fsum(j*log_coeff[j]*coeff[k-j] for j in range(1,k+1))/k)
    return coeff


def F_asymptotic(s, u, a, cutoff=64, order=40):
    c = mp.gamma(a)/mp.gamma(a+u)
    d = gamma_ratio_coeffs(u,order)
    finite = mp.fsum(mp.gamma(n+a+u)/mp.gamma(n+a)/(n+a)**s for n in range(cutoff))
    tail = mp.fsum(d[k]*mp.zeta(s-u+k,cutoff+a) for k in range(order))
    return c*(finite+tail)


def D_asymptotic(s,u,a,cutoff=64,order=40):
    c=mp.gamma(a)/mp.gamma(a+u)
    d=gamma_ratio_coeffs(u,order)
    finite=mp.fsum(mp.gamma(n+a+u)/mp.gamma(n+a)/(n+a)**s-mp.gamma(n+1+u)/mp.gamma(n+1)/mp.power(n+1,s) for n in range(cutoff))
    tail=mp.fsum(d[k]*(mp.zeta(s-u+k,cutoff+a)-mp.zeta(s-u+k,cutoff+1)) for k in range(order))
    return c*(finite+tail)


def T_exact(m,u,a):
    return -mp.fsum(int(sp.functions.combinatorial.numbers.stirling(m+1,j,kind=2))*mp.ff(a-1,j)/(u+j) for j in range(1,m+2))


def correction_coeff(m,r,a):
    return (-1)**(r+1)*mp.fsum(int(sp.functions.combinatorial.numbers.stirling(m+1,j,kind=2))*mp.ff(a-1,j)/mp.mpf(j)**(r+1) for j in range(1,m+2))


def encode(x):
    return {'real':mp.nstr(mp.re(x),60),'imag':mp.nstr(mp.im(x),60)}


def run():
    started=time.time()
    results=[]
    def save(kind,params,lhs,rhs):
        err=abs(lhs-rhs)
        results.append({'kind':kind,'parameters':params,'lhs':encode(lhs),'rhs':encode(rhs),'absolute_error':mp.nstr(err,8)})
        print(kind, params, 'error',mp.nstr(err,5),flush=True)
    for a in [mp.mpf('0.5'),mp.mpf('1.3'),mp.mpc('1.2','0.4')]:
        for u in [mp.mpf('-0.17'),mp.mpc('0.15','0.12')]:
            t=mp.mpf('.63')
            z=mp.exp(-t)
            lhs=z**a*mp.hyp2f1(1,a+u,a,z)
            K=mp.gamma(a)*mp.gamma(1+u)/mp.gamma(a+u)
            rhs=K*z/(1-z)**(1+u)-(a-1)/(1+u)*z**a*mp.hyp2f1(1,a+u,2+u,1-z)
            save('hypergeometric_connection',{'a':str(a),'u':str(u)},lhs,rhs)
            for m in range(5):
                lhs=D_asymptotic(-m,u,a)
                rhs=T_exact(m,u,a)
                save('entire_difference_negative_integer',{'m':m,'a':str(a),'u':str(u),'N':64,'K':40},lhs,rhs)
    # Higher-accuracy repeat explicitly audits sensitivity to truncating the
    # independent Gamma-ratio tail, including a complex parameter case.
    for m,a,u in [(4,mp.mpf('.5'),mp.mpf('-.17')),(3,mp.mpc('1.2','.4'),mp.mpc('.15','.12'))]:
        lhs=D_asymptotic(-m,u,a,96,48)
        rhs=T_exact(m,u,a)
        save('larger_tail_repeat',{'m':m,'a':str(a),'u':str(u),'N':96,'K':48},lhs,rhs)
    # At s=1 the termwise difference is ordinarily convergent, although each
    # separate height-one series generally diverges.
    for a,u in [(mp.mpf('.5'),mp.mpc('.15','.12')),(mp.mpc('1.2','.4'),mp.mpf('-.17'))]:
        K=mp.gamma(a)*mp.gamma(1+u)/mp.gamma(a+u)
        save('s_one_convergent_difference',{'a':str(a),'u':str(u)},D_asymptotic(1,u,a),(K-1)/u)
    # Local Taylor coefficients of the analytic Gauss connection block are
    # checked against the finite Stirling rule, without asymptotic tails.
    for a in [mp.mpf('.5'),mp.mpc('1.2','.4')]:
        for m in range(4):
            for r in range(4):
                def block(t,u):
                    return -(a-1)/(1+u)*mp.exp(-a*t)*mp.hyp2f1(1,a+u,2+u,-mp.expm1(-t))
                # mp.diff evaluates derivatives directly rather than using the
                # Stirling-expression coefficients.
                lhs=(-1)**m*mp.diff(lambda u: mp.diff(lambda t:block(t,u),0,m),0,r)/mp.factorial(r)
                rhs=correction_coeff(m,r,a)
                save('mixed_kernel_coefficient',{'m':m,'r':r,'a':str(a)},lhs,rhs)
    report={'working_decimal_digits':mp.mp.dps,'certificate':False,'method':'Gamma-ratio asymptotic continuation, independent Gauss kernel identity, and direct mixed differentiation','count':len(results),'elapsed_seconds':time.time()-started,'max_absolute_error':mp.nstr(max(mp.mpf(x['absolute_error']) for x in results),10),'checks':results}
    (HERE.parent/'results'/ 'shifted_height_one_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('DONE',report['count'],report['max_absolute_error'],report['elapsed_seconds'],flush=True)

if __name__=='__main__':
    run()
