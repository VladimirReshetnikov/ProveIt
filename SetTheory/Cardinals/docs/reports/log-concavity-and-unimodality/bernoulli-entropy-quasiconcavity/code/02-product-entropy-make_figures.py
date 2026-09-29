#!/usr/bin/env python3
"""Regenerate the two illustrative profile plots. Requires Matplotlib.

Only illustrations use floating point. The exact verifier is separate.
"""
from pathlib import Path
import csv
import math
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]

def profile(q: float) -> float:
    if not 0<q<1:
        raise ValueError('q must lie strictly between zero and one')
    a=1-q
    lo,hi=0.0,1.0
    while math.tanh(a*hi)*math.tanh(hi)<a:
        hi*=2
    for _ in range(80):
        mid=(lo+hi)/2
        if math.tanh(a*mid)*math.tanh(mid)<a:
            lo=mid
        else:
            hi=mid
    t=(lo+hi)/2
    beta=(math.sinh(a*t)/math.cosh(t))**2
    return q*beta/(a+beta)

def main() -> None:
    (ROOT/'figures').mkdir(exist_ok=True)
    (ROOT/'results').mkdir(exist_ok=True)
    orders=[i/1000 for i in range(1,1000)]
    values=[profile(q) for q in orders]
    with (ROOT/'results'/'profile_plot.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['q','Psi_approx'])
        writer.writerows(zip(orders,values))
    fig,ax=plt.subplots(figsize=(7.2,3.8))
    ax.plot(orders,values,label=r'$\Psi(q)$')
    ax.axhline(1/9,linestyle=':',label='Nine-bit bound: 1/9')
    ax.axhline(1/10,linestyle='--',label='Ten-bit boundary: 1/10')
    ax.set(xlabel='Entropy order q',ylabel='Maximum curvature ratio',xlim=(0,1),ylim=(0,0.12))
    ax.legend(loc='lower center',fontsize=9);ax.grid(alpha=0.25)
    fig.tight_layout();fig.savefig(ROOT/'figures'/'profile.pdf');plt.close(fig)
    orders=[0.48+i/100000 for i in range(3001)]
    fig,ax=plt.subplots(figsize=(7.2,3.8))
    ax.plot(orders,[profile(q) for q in orders],label=r'$\Psi(q)$')
    ax.axhline(0.1,linestyle='--',label='Ten-bit boundary')
    ax.scatter([20/41,0.5],[profile(20/41),0.1],label='Certified order 20/41; exact order 1/2')
    ax.set(xlabel='Entropy order q',ylabel='Maximum curvature ratio',xlim=(0.48,0.51))
    ax.ticklabel_format(axis='y',style='plain',useOffset=False)
    ax.legend(loc='lower center',fontsize=9);ax.grid(alpha=0.25)
    fig.tight_layout();fig.savefig(ROOT/'figures'/'ten_bit_detail.pdf');plt.close(fig)
    print('Wrote both vector figures and the numerical profile CSV.')

if __name__=='__main__':
    main()
