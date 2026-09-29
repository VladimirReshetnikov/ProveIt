#!/usr/bin/env python3
"""Floating-point Fourier checks of geometric-uniform entropy asymptotics.

This is a numerical diagnostic, NOT interval arithmetic or proof of a remainder.
Small negative Fourier reconstruction values are clipped and their mass reported.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
import numpy as np
from scipy.special import xlogy, ndtr


def entropy_deficit(q: float, grid_power: int = 17, modes: int = 4096) -> dict:
    if not 0.0 < q < 1.0:
        raise ValueError('q must lie strictly between zero and one.')
    if grid_power < 10 or modes < 1 or modes >= 2**(grid_power-1):
        raise ValueError('Insufficient real-space grid for the selected Fourier modes.')
    n=2**grid_power
    radius=np.sqrt(3*(1+q)/(1-q))
    beta=np.sqrt(3*(1-q*q))
    t=np.pi*np.arange(modes+1)/radius
    cf=np.ones(modes+1)
    scale=1.0
    depth=0
    while beta*scale*t[-1] > 1e-5:
        cf *= np.sinc(beta*scale*t/np.pi)
        scale *= q
        depth += 1
        if depth > 200000:
            raise RuntimeError('Product depth exceeded safety limit.')
    # Remaining independent scaled copy: keep its exact variance contribution.
    cf *= np.exp(-0.5*scale*scale*t*t)
    spectrum=np.zeros(n//2+1)
    spectrum[:modes+1]=cf
    density=np.fft.fftshift(np.fft.irfft(spectrum,n=n))*n/(2*radius)
    x=(np.arange(n)-n//2)*(2*radius/n)
    dx=2*radius/n
    negative_mass=float(-np.minimum(density,0).sum()*dx)
    density=np.maximum(density,0)
    mass=float(density.sum()*dx)
    variance=float((density*x*x).sum()*dx)
    # Integrate the nonnegative, affine-renormalized entropy integrand.
    # Outside |x|<=9 the theorem's envelope makes the exact integral tiny.
    keep=np.abs(x)<=min(radius,9.0)
    normal=np.exp(-0.5*x[keep]**2)/np.sqrt(2*np.pi)
    ratio=density[keep]/normal
    u=ratio-1
    value=xlogy(ratio,ratio)-ratio+1
    small=np.abs(u)<0.25
    value[small]=sum((-1)**k*u[small]**k/(k*(k-1)) for k in range(2,26))
    deficit=float((normal*value).sum()*dx)
    if radius <= 9:
        # Density vanishes outside the exact compact support. Add that part
        # of the affine-renormalized integrand analytically. On the symmetric
        # grid, one included endpoint equals two half-weight endpoints.
        deficit+=2*ndtr(-radius)
    # For radius>9 the omitted entropy integral is not set to zero by theorem;
    # it is simply below this floating-point diagnostic's useful precision.

    return {'q':q,'epsilon':1-q,'deficit':deficit,'negative_mass_clipped':negative_mass,
            'mass_before_normalization':mass,'variance':variance,
            'grid_points':n,'fourier_modes':modes,'product_depth':depth,
            'last_mode_absolute_value':float(abs(cf[-1]))}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data'))
    args=parser.parse_args()
    coeff_path=args.output/'exact_coefficients.json'
    if not coeff_path.exists():
        raise FileNotFoundError('Run coefficients.py first.')
    from fractions import Fraction
    coefficients={int(n):float(Fraction(v)) for n,v in json.loads(coeff_path.read_text())['kl'].items()}
    if not set(range(2,9)).issubset(coefficients):
        raise ValueError('Numerical comparisons require coefficients through order 8.')
    rows=[]
    for q in [0.8,0.85,0.9,0.93,0.95,0.97,0.98,0.99]:
        row=entropy_deficit(q,17,4096)
        check=entropy_deficit(q,18,8192)
        e=1-q
        row['grid_spectral_change']=check['deficit']-row['deficit']
        for order in [3,4,5,8]:
            prediction=sum(coefficients[n]*e**n for n in range(2,order+1))
            row[f'prediction_{order}']=prediction
            row[f'residual_{order}']=row['deficit']-prediction
        row['quartic_scaled_residual']=(row['deficit']-row['prediction_3'])/e**4
        rows.append(row)
    args.output.mkdir(parents=True,exist_ok=True)
    with (args.output/'numerical_checks.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    print('q       deficit              cubic              through d8         grid change')
    for r in rows:
        print(f"{r['q']:.2f}  {r['deficit']:.15g}  {r['prediction_3']:.12g}  {r['prediction_8']:.12g}  {r['grid_spectral_change']:.3g}")
    print('max clipped mass',max(r['negative_mass_clipped'] for r in rows))
    print('max variance error',max(abs(r['variance']-1) for r in rows))

if __name__=='__main__': main()
