#!/usr/bin/env python3
"""Reproduce numerical illustrations; these are NOT the exact certificate.
Requires mpmath. Run from the package directory:
    python code/experiments.py --output results/numerics.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp
from certify import partitions
from series import coefficients, inverse_coefficients


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    mp.mp.dps = 130
    c = mp.pi*mp.sqrt(mp.mpf(2)/3)
    a = mp.mpf(1)/24
    delta = a+2/c**2
    p = partitions(2001)
    def Hinv(y):
        return 6/mp.pi**2*mp.lambertw(
            -mp.pi/(2*mp.sqrt(2)*mp.power(3,mp.mpf(3)/4)*mp.sqrt(y)),-1)**2
    def vfun(z):
        v = mp.mpf(1)
        for _ in range(500):
            new = -mp.log1p(-z)/z-2*mp.log1p(-z*z*v)/z
            if abs(new-v) < mp.mpf('1e-115'):
                return new
            v = new
        raise ArithmeticError('fixed point did not converge')
    def smooth_bias(n):
        mu = c*mp.sqrt(n-a); z = 1/mu; v = vfun(z)
        B = a+(2*v-z*z*v*v)/c**2
        A = ((1-z*z*v)**2*(1-2*z)/
             ((1-2*z-z*z*v)*(1-z)))
        return mu,B,A
    def fmt(x):return mp.nstr(x,35)
    samples = []
    for n in list(range(2,16))+[20,30,50,100,400,401,1000,1001,2000,2001]:
        d = n-Hinv(mp.mpf(p[n]))
        row = {'n':n,'p_n':str(p[n]),'bias':fmt(d)}
        if n>=100:
            mu,B,A=smooth_bias(n)
            predicted = -((-1)**n)*mp.sqrt(2)*mu/c**2*A*mp.exp(-mu/2)
            row['smooth_bias']=fmt(B)
            row['arithmetic_residual']=fmt(d-B)
            row['parity_prediction_ratio']=fmt((d-B)/predicted)
        samples.append(row)
    # Check forward and inverse coefficient families numerically.
    _,w=coefficients(12);_,r=inverse_coefficients(12)
    series_checks=[]
    for n in [400,1000,2000]:
        mu,B,A=smooth_bias(n)
        approx = delta+sum(mp.mpf(t.numerator)/t.denominator/mu**j
                           for j,t in enumerate(w) if j)/c**2
        # A rigorous analytic bound, evaluated numerically only in this file.
        tail = (mp.mpf(129)/256/c**2)*(20/mu)**13/(1-20/mu)
        assert abs(B-approx) < tail
        y = mp.exp(mu)/(4*mp.sqrt(3)*(n-a))*(1-1/mu)
        u = Hinv(y); t = c*mp.sqrt(u)
        invapprox = u+delta+sum(mp.mpf(b.numerator)/b.denominator/t**j
                                for j,b in enumerate(r) if j)/c**2
        series_checks.append({'n':n,'bias_12_term_error':fmt(B-approx),
                              'inverse_12_term_error':fmt(n-invapprox),
                              'bias_Cauchy_error_bound':fmt(tail)})
    # Exhaustive small integer-input test of the one-comparison staircase formula.
    # This is independent numerical evidence, not needed by the proof.
    true_index=10
    tested=0
    for y in range(42,5001):
        while p[true_index] < y:true_index+=1
        k=int(mp.floor(Hinv(y)+delta))+1
        result=k if p[k]>=y else k+1
        assert result==true_index
        tested+=1
    result={'status':'PASS (numerical, not interval-certified)',
            'mpmath_decimal_precision':mp.mp.dps,
            'bias_samples':samples,'series_checks':series_checks,
            'staircase_integer_inputs_tested':tested,
            'staircase_range':[42,5000]}
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
