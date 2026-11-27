#!/usr/bin/env python3
"""Reproduce finite numerical illustrations of the proved sampling obstruction.

This script does not establish the infinite theorem. Its proof is in the report.
Dependencies: mpmath (tested with mp.dps=80). Run from any directory; optional
--output writes JSON and a table of the first coefficients.
"""
import argparse
import csv
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80


def F(x, p):
    x = mp.mpf(x)
    return x * mp.log(x) + mp.mpf('0.5') * x ** (1 - mp.mpf(2)/p) * mp.sin(mp.pi*x**(mp.mpf(1)/p))**2


def coefficient(n, p):
    if n == 1:
        return F(2, p)
    return n * (F(n+1, p)-2*F(n,p)+F(n-1,p))


def interpolated_remainder(x, p):
    x = mp.mpf(x)
    m = int(mp.floor(x))
    w = x-m
    interpolant = (1-w)*F(m,p)+w*F(m+1,p)
    return interpolant/x-mp.log(x)


def leading_remainder(x, p):
    x = mp.mpf(x)
    return mp.mpf('0.5')*x**(-mp.mpf(2)/p)*mp.sin(mp.pi*x**(mp.mpf(1)/p))**2


def original_ramp_remainder(x,p):
    x = mp.mpf(x)
    return mp.fsum(coefficient(n,p)*(mp.mpf(1)/n-1/x) for n in range(1,int(mp.floor(x))+1))-mp.log(x)


def run():
    results = []
    rows = []
    for p in (4,5,8):
        aa = [coefficient(n,p) for n in range(1,1001)]
        assert all(0<a<4 for a in aa)
        samples = [abs(interpolated_remainder(mp.mpf(m)**p,p)) for m in range(1,21)]
        assert max(samples) < mp.mpf('1e-70')
        max_scaled_error = mp.mpf(0)
        for n in range(1,101):
            for u in (mp.mpf('0.1'),mp.mpf('0.5'),mp.mpf('0.9')):
                x = n+u
                delta = interpolated_remainder(x,p)-leading_remainder(x,p)
                assert -mp.mpf('1e-70') <= delta <= 1/(2*x*x)
                max_scaled_error = max(max_scaled_error,x*x*delta)
        ramp_identity_errors = [abs(original_ramp_remainder(x,p)-interpolated_remainder(x,p))
                                for x in (mp.mpf('1.5'),mp.mpf('10.25'),mp.mpf('100.5'))]
        assert max(ramp_identity_errors) < mp.mpf('1e-70')
        results.append({
            'p':p,
            'pole':str(1-mp.mpf(2)/p),
            'proved_residue':'1/4',
            'minimum_first_1000_coefficients':mp.nstr(min(aa),30),
            'maximum_first_1000_coefficients':mp.nstr(max(aa),30),
            'maximum_absolute_sample_residual_first_20':mp.nstr(max(samples),5),
            'maximum_x_squared_interpolation_error_tested':mp.nstr(max_scaled_error,30),
            'maximum_ramp_identity_error_tested':mp.nstr(max(ramp_identity_errors),5),
        })
        rows.extend((p,n,mp.nstr(a,40)) for n,a in enumerate(aa,1))
    return {'precision_decimal_digits':mp.mp.dps,
            'interpretation':'Finite numerical verification only; proof supplies all infinite claims.',
            'results':results},rows


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    report,rows=run()
    if args.output:
        args.output.mkdir(parents=True,exist_ok=True)
        (args.output/'sampling_verification.json').write_text(json.dumps(report,indent=2)+'\n')
        with (args.output/'sampling_coefficients.csv').open('w',newline='') as f:
            writer=csv.writer(f)
            writer.writerow(('p','n','a_n_decimal'))
            writer.writerows(rows)
    print(json.dumps(report,indent=2))
