#!/usr/bin/env python3
"""Numerical checks of lattice maximization, NOT of the avoidance theorem."""
from __future__ import annotations
import csv
import math
from pathlib import Path
from approximation import lattice_phi, constants, log_mean

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    for p in (0.1,0.25,0.5,0.75,0.9):
        a=-math.log(p);q=1-p
        min_phi=4*a*a/(q*q)*math.exp(-2*a/q)
        theta_min=(math.log(2*a/q)/a)%1
        theta_max=(math.log(2)/a)%1
        assert abs(lattice_phi(p,theta_min)-min_phi)<2e-14
        assert abs(lattice_phi(p,theta_max)-4/math.exp(2))<2e-14
        for k in range(1001):
            theta=k/1000
            vals=[]
            for j in range(-100,101):
                x=math.exp(a*(theta-j))
                vals.append(x*x*math.exp(-x))
            assert abs(lattice_phi(p,theta)-max(vals))<2e-14
    rows=[]
    p=0.5;a=-math.log(p);c=constants(p)['c_p']
    for exponent in (3,6,12,24,48,96,192,384,768):
        n=10**exponent;L=math.log(n)
        t=(2*L-math.log(L)+math.log((1-p)*a/4))/a
        candidates=[]
        for r in range(max(2,math.floor(t)-20),math.floor(t)+21):
            lm=log_mean(n,r,p)
            if lm>math.log(1000):
                val=0.0
            else:
                lam=math.exp(lm)
                val=c*math.exp(2*lm-lam)*(r/L)**2
            candidates.append(val)
        predicted=4*c/a**2*lattice_phi(p,t%1)
        rows.append(dict(n_power_of_10=exponent,p=p,phase=t%1,
                         normalized_exact_mean_correction_max=max(candidates),
                         limiting_lattice_amplitude=predicted,
                         difference=max(candidates)-predicted))
    with (ROOT/'results/lattice_diagnostics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print('PASS: 5,005 lattice comparisons and 10 extremum identities (floating point).')
    print('The CSV compares formula coefficients, not measured probabilities.')

if __name__=='__main__':
    main()
