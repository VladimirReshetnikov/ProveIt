#!/usr/bin/env python3
"""Independent high-precision checks for the falling-factorial cover saddle.

Run: python check_saddle.py --ns 20 50 100 200 500 1000 --dps 80 --order 3
Outputs JSON and text under the explicitly selected --output-dir.
Floating-point tail evaluations are diagnostics, not rigorous interval certificates.
Dependencies: Python >=3.9, mpmath (tested with 1.3.0).

The saddle is differentiated using the two explicit roots of each quadratic.
The integer sum is evaluated independently using log-gamma factorial ratios,
log-scaled positive summation, and an analytic geometric upper-tail bound from
strict concavity of the same positive-term interpolant. No quadrature is used.
"""
import argparse
import json
import math
from pathlib import Path
import mpmath as mp


def root_data(n):
    return [(1 + mp.sqrt(1+8*j))/2 for j in range(n)]


def f(n,t,roots):
    # M(t)-j = (t-r_j)(t-(1-r_j))/2, positive in the saddle domain.
    return mp.fsum(mp.log(t-r)+mp.log(t-1+r) for r in roots)-n*mp.log(2)-mp.loggamma(t+1)


def deriv(t,j,roots):
    total=mp.fsum((t-r)**(-j)+(t-1+r)**(-j) for r in roots)
    return (-1)**(j-1)*mp.factorial(j-1)*total-mp.polygamma(j-1,t+1)


def saddle(n,roots):
    # f' is strictly decreasing, diverges at the lower root, tends to -infinity.
    root=roots[-1]
    lo=root+mp.mpf('0.0001')
    hi=max(root+1,2*n/mp.lambertw(2*n))
    while deriv(hi,1,roots)>0: hi*=2
    x=(lo+hi)/2
    tolerance=mp.power(10,-mp.mp.dps+15)
    for _ in range(400):
        fp=deriv(x,1,roots)
        step=fp/deriv(x,2,roots)
        if abs(step)<tolerance*max(1,abs(x)): return x-step
        if fp>0: lo=x
        else: hi=x
        proposal=x-step
        if not lo < proposal < hi: proposal=(lo+hi)/2
        if abs(proposal-x)<tolerance*max(1,abs(x)): return proposal
        x=proposal
    raise RuntimeError('saddle iteration did not converge')


def odd_double_factorial(k):
    return math.prod(range(1,k+1,2)) if k>0 else 1


def correction(level,lambdas):
    if level==0: return mp.mpf(1)
    target=2*level
    result=[]
    # weight w represents derivative j=w+2 and multiplicity k_j.
    def visit(w,remaining,degree,product):
        if w>target:
            if remaining==0: result.append(odd_double_factorial(degree-1)*product)
            return
        j=w+2
        base=lambdas[j]/mp.factorial(j)
        for k in range(remaining//w+1):
            visit(w+1,remaining-w*k,degree+j*k,product*base**k/mp.factorial(k))
    visit(1,target,0,mp.mpf(1))
    return mp.fsum(result)


def integer_logterm(n,m):
    M=m*(m-1)//2
    if M<n: return mp.ninf
    return mp.loggamma(M+1)-mp.loggamma(M-n+1)-mp.loggamma(m+1)


def exact_logsum(n,scale):
    # Smallest integer m with M(m)>=n; earlier terms vanish identically.
    m=(1+math.isqrt(1+8*n))//2
    while m*(m-1)//2<n: m+=1
    first=m
    terms=[]
    goal=mp.power(10,-mp.mp.dps+15)
    while True:
        logterm=integer_logterm(n,m)
        term=mp.exp(logterm-scale)
        terms.append(term)
        lognext=integer_logterm(n,m+1)
        q=mp.exp(lognext-logterm)
        if q<1:
            # Strict log concavity implies every later consecutive ratio <=q.
            tail_upper=term*q/(1-q)
            total=mp.fsum(terms)
            if tail_upper<goal*total:
                return scale+mp.log(total)-1, {'first_m':first,'last_m':m,'relative_tail_bound':tail_upper/total}
        m+=1
        if m>1000000: raise RuntimeError('sum did not converge')


def numeric_case(n,K):
    if not isinstance(n,int) or not 2 <= n <= 10000 or not 0 <= K <= 3:
        raise ValueError('supported domain: 2 <= n <= 10000 and 0 <= order <= 3')
    roots=root_data(n)
    tau=saddle(n,roots)
    ft=f(n,tau,roots)
    sigma=mp.sqrt(-1/deriv(tau,2,roots))
    lambdas={j:deriv(tau,j,roots)*sigma**j for j in range(3,2*K+3)}
    corrections=[correction(l,lambdas) for l in range(K+1)]
    logH,meta=exact_logsum(n,ft)
    # Independent whole sum for the adjacent n, rather than a termwise shortcut.
    logHprev,prevmeta=exact_logsum(n-1,ft)
    logleading=ft-1+mp.log(mp.sqrt(2*mp.pi)*sigma)
    w=mp.lambertw(2*n)
    errors=[]
    for k in range(K+1):
        approx_over_exact=mp.exp(logleading-logH)*mp.fsum(corrections[:k+1])
        err=approx_over_exact-1
        errors.append({'K':k,'relative_error_approx_minus_exact':err,'scaled_error_n_pow_K_plus_1':err*n**(k+1)})
    return {
        'n':n,'tau':tau,'sigma':sigma,'log_H_n':logH,
        'saddle_residual':deriv(tau,1,roots),
        'derivative_scaled':{str(j):lambdas[j]*mp.mpf(n)**(mp.mpf(j)/2-1) for j in lambdas},
        'corrections':corrections,'errors':errors,
        'ratio_H_prev_over_H':mp.exp(logHprev-logH),
        'ratio_normalized_by_W_squared_over_n_squared':mp.exp(logHprev-logH)*n*n/(w*w),
        'ratio_normalized_by_W_squared_over_2n_squared':2*mp.exp(logHprev-logH)*n*n/(w*w),
        'sum_metadata':meta,'previous_sum_metadata':prevmeta,
    }


def stringify(obj):
    if isinstance(obj,mp.mpf): return mp.nstr(obj,50)
    if isinstance(obj,dict): return {k:stringify(v) for k,v in obj.items()}
    if isinstance(obj,list): return [stringify(v) for v in obj]
    return obj


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ns',type=int,nargs='+',default=[20,50,100,200,500,1000])
    p.add_argument('--dps',type=int,default=80)
    p.add_argument('--order',type=int,default=3)
    p.add_argument('--output-dir',required=True)
    args=p.parse_args()
    if not 40 <= args.dps <= 200 or not 0 <= args.order <= 3 or any(n < 2 or n > 10000 for n in args.ns):
        p.error('require 40 <= dps <= 200, 0 <= order <= 3, and 2 <= n <= 10000')
    path=Path(args.output_dir)
    if path.exists(): p.error('output directory must not exist')
    path.mkdir(parents=True)
    mp.mp.dps=args.dps
    cases=[]
    lines=[f'mpmath {mp.__version__}; decimal precision {args.dps}; K=0..{args.order}',
           'Error convention: approximation / exact integer sum - 1.',
           'R = (H_(n-1)/H_n) / (W(2n)^2/n^2), expected limit 1/2.',
           'n, tau, sigma, R, scaled_errors_K_0_up']
    for n in args.ns:
        row=numeric_case(n,args.order)
        cases.append(row)
        line=', '.join([str(n),mp.nstr(row['tau'],11),mp.nstr(row['sigma'],11),mp.nstr(row['ratio_normalized_by_W_squared_over_n_squared'],11)]+[mp.nstr(e['scaled_error_n_pow_K_plus_1'],11) for e in row['errors']])
        lines.append(line)
        print(line,flush=True)
    lines+=['','Scaled derivatives lambda_j*n^(j/2-1); j=3..'+str(2*args.order+2)]
    for row in cases:
        lines.append(str(row['n'])+': '+', '.join('j'+j+'='+mp.nstr(v,10) for j,v in row['derivative_scaled'].items()))
    lines+=['','Floating-point relative truncation error and evaluated tail majorant (not intervals):']
    for row in cases:
        lines.append(str(row['n'])+': errors='+','.join(mp.nstr(e['relative_error_approx_minus_exact'],9) for e in row['errors'])+'; m='+str(row['sum_metadata']['first_m'])+'..'+str(row['sum_metadata']['last_m'])+'; tail<'+mp.nstr(row['sum_metadata']['relative_tail_bound'],5))
    (path/'numeric_results.json').write_text(json.dumps({'dps':args.dps,'max_K':args.order,'cases':stringify(cases)},indent=2)+'\n')
    (path/'numeric_summary.txt').write_text('\n'.join(lines)+'\n')

if __name__=='__main__': main()
