#!/usr/bin/env python3
"""Supplementary audits: derivatives, endpoint curvature and multinomial core.

Run from any working directory: python code/verify_supplement.py
Requires the sibling verify.py, mpmath and sympy. These floating-point tests
are not outward-rounded interval certificates.
"""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from verify import (exact_log, core_log, f_derivative, modular_M,
                    half_analytic_log, optimal_K, error_bounds)

ROOT = Path(__file__).resolve().parents[1]

def kernel(t: mp.mpf) -> mp.mpf:
    return mp.log(mp.expm1(t) / t) if t else mp.mpf(0)

def primitive(t: mp.mpf) -> mp.mpf:
    if not t:
        return mp.mpf(0)
    return t*t/2 + mp.polylog(2, mp.exp(-t)) - mp.pi**2/6 - t*mp.log(t) + t

def multinomial_approx(h: mp.mpf, x: mp.mpf,
                       weights: list[mp.mpf], order: int) -> mp.mpf:
    if h <= 0 or x < 0 or order < 1 or any(w <= 0 for w in weights):
        raise ValueError('Positive h, weights and order, nonnegative x required')
    total = mp.fsum(weights)
    t = h*x
    def balanced(function):
        return (function(total*t) - mp.fsum(function(w*t) for w in weights)
                + (len(weights)-1)*function(mp.mpf(0)))
    classical = mp.loggamma(total*x+1) - mp.fsum(mp.loggamma(w*x+1) for w in weights)
    corr = mp.fsum(mp.bernoulli(2*k)*h**(2*k-1)/mp.factorial(2*k)
                   * balanced(lambda u: f_derivative(u, 2*k-1))
                   for k in range(1, order+1))
    return classical + balanced(primitive)/h + balanced(kernel)/2 + corr

def multinomial_finite_log(h: mp.mpf, indices: list[int]) -> mp.mpf:
    if h <= 0 or any(n < 0 or int(n) != n for n in indices):
        raise ValueError('Positive h and nonnegative integer indices required')
    def factorial_log(n):
        return mp.fsum(mp.log(mp.expm1(h*j)) for j in range(1,n+1))
    return factorial_log(sum(indices)) - mp.fsum(factorial_log(n) for n in indices)

def exact_derivative(h: mp.mpf, x: mp.mpf) -> mp.mpf:
    n = int(mp.ceil((mp.mp.dps+12)*mp.log(10)/h))
    return 2*h*x + 2*h*mp.fsum(mp.exp(-h*m*x)*(-mp.expm1(-h*m*x))
                               /mp.expm1(h*m) for m in range(1,n+1))

def approx_derivative(h: mp.mpf, x: mp.mpf, order: int) -> mp.mpf:
    if x <= 0:
        raise ValueError('The derivative audit uses x>0')
    t = h*x
    core = 2*mp.digamma(2*x+1) - 2*mp.digamma(x+1)
    phase = t + 2*mp.log(mp.cosh(t/2))
    amplitude = h*(1/t-1/mp.sinh(t))/2
    terms = mp.fsum(mp.bernoulli(2*k)*h**(2*k)/mp.factorial(2*k)
                   *(2*f_derivative(2*t,2*k)-2*f_derivative(t,2*k))
                   for k in range(1,order+1))
    return core + phase + amplitude + terms

def main() -> None:
    mp.mp.dps = 100
    output = {'precision_digits':100, 'interval_arithmetic':False,
              'multinomial':[], 'endpoint_curvature':[], 'half_sheets':[],
              'relative_derivative':[]}
    def text(v):
        return mp.nstr(v,35)
    h = mp.mpf(1)
    order = optimal_K(h)
    for raw_weights, raw_x in [(['1','1','1'],'1'), (['0.5','1','1.5'],'2')]:
        weights = list(map(mp.mpf,raw_weights))
        x = mp.mpf(raw_x)
        indices = [int(w*x) for w in weights]
        exact = multinomial_finite_log(h,indices)
        approx = multinomial_approx(h,x,weights,order)
        bound = len(weights)/2 * error_bounds(h,order)[0]
        error = abs(exact-approx)
        assert error < bound
        output['multinomial'].append({'h':'1','weights':raw_weights,'x':raw_x,
                                      'error':text(error),'bound':text(bound)})
    for hs in ['1','0.5']:
        h = mp.mpf(hs)
        n = int(mp.ceil((mp.mp.dps+12)*mp.log(10)/h))
        direct = h+h*h*mp.fsum(m/mp.expm1(h*m) for m in range(1,n+1))
        action = 4*mp.pi**2
        r = mp.exp(-action/h)
        # Sum N*sigma_{-1}(N) through its equivalent Lambert sum.
        modular = action*mp.fsum(m*r**m/(1-r**m) for m in range(1,20))
        predicted = mp.pi**2/6+h/2+h*h/24-modular
        error = abs(direct-predicted)
        assert error < mp.mpf('1e-88')
        output['endpoint_curvature'].append({'h':hs,'a':text(direct),
                                             'identity_error':text(error)})
    h = mp.mpf(1)
    for n in [1,2]:
        analytic = half_analytic_log(h)
        for j in range(n):
            x = mp.mpf(j)+mp.mpf('.5')
            analytic += (h*(2*x+1) + mp.log(-mp.expm1(-h*(2*x+1)))
                         + mp.log(-mp.expm1(-h*(2*x+2)))
                         - 2*mp.log(-mp.expm1(-h*(x+1))))
        exact,_ = exact_log(h,mp.mpf(n)+mp.mpf('.5'))
        defect = exact-analytic
        predicted = 4*modular_M(h)-2*modular_M(h/2)
        assert abs(defect-predicted) < mp.mpf('1e-88')
        output['half_sheets'].append({'x':str(n+.5),'defect':text(defect)})
    for xs in ['0.01','2']:
        x = mp.mpf(xs)
        error = abs(exact_derivative(h,x)-approx_derivative(h,x,order))
        core_prime = 2*mp.digamma(2*x+1)-2*mp.digamma(x+1)
        bound = error_bounds(h,order)[1]*core_prime
        assert error < bound
        output['relative_derivative'].append({'h':'1','x':xs,'error':text(error),
                                              'bound':text(bound)})
    output['all_passed'] = True
    destination = ROOT/'data'/'verification_supplement.json'
    destination.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(output,indent=2))

if __name__ == '__main__':
    main()
