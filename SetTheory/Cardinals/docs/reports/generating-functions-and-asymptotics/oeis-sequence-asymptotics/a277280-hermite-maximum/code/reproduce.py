"""Regenerate the article's numerical tables, figures, and computed b-file.

Run: python code/reproduce.py
Dependencies: mpmath, numpy, matplotlib.
"""
from __future__ import annotations
import csv
from pathlib import Path
import sys
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from a277280 import (maximizing_exponent, log_values, correction_polynomials,
                     ratio_fraction, iter_terms)

ROOT = Path(__file__).resolve().parents[1]
DATA, FIG = ROOT/'data', ROOT/'figures'
DATA.mkdir(exist_ok=True)
FIG.mkdir(exist_ok=True)
mp.mp.dps = 70


def save_figure(name):
    plt.tight_layout()
    plt.savefig(FIG/(name+'.pdf'), bbox_inches='tight')
    plt.savefig(FIG/(name+'.png'), dpi=170, bbox_inches='tight')
    plt.close()


def latex_number(x, digits=3):
    if x == 0:
        return '0'
    exponent = int(mp.floor(mp.log10(abs(x))))
    mantissa = x / mp.power(10, exponent)
    return rf'{float(mantissa):.{digits}f}\times 10^{{{exponent}}}'


indices = [10,100,1000,10000,10**6,10**8,10**12]
rows, tex = [], []
for n in indices:
    la, ll, delta = log_values(n, 70)
    s = mp.sqrt(2*n)
    p1,p2,p3 = correction_polynomials(delta)
    quotient = mp.exp(la-ll)
    err1 = mp.expm1(la-ll-p1/s)
    err2 = mp.expm1(la-ll-p1/s-p2/s**2)
    err3 = mp.expm1(la-ll-p1/s-p2/s**2-p3/s**3)
    rows.append([n, maximizing_exponent(n), *[mp.nstr(x,40) for x in
                 [delta, quotient, err1, err2, err3]]])
    nlabel = str(n) if n < 10**6 else rf'10^{{{int(mp.log10(n))}}}'
    tex.append(rf'${nlabel}$ & {maximizing_exponent(n):,} & '
               rf'${float(quotient):.10f}$ & ${latex_number(err1)}$ & '
               rf'${latex_number(err2)}$ \\')
with (DATA/'asymptotic_comparison.csv').open('w',newline='') as f:
    w=csv.writer(f)
    w.writerow(['n','maximizing_exponent','delta','a_over_L',
                'a_over_L1_minus_1','a_over_L2_minus_1','a_over_L3_minus_1'])
    w.writerows(rows)
(DATA/'table_rows.tex').write_text('\n'.join(tex)+'\n' + r'\bottomrule' + '\n')

if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
with (DATA/'computed_b277280_0_1000.txt').open('w') as f:
    f.write('# Independently computed by code/a277280.py; not a downloaded OEIS b-file.\n')
    for n,d,value in iter_terms(1000):
        f.write(f'{n} {value}\n')

# Figure 1: direct exact-ratio formulas, evaluated as floats for plotting.
ns=np.arange(100,10001)
ratios=[]
for n in ns:
    numerator,denominator=ratio_fraction(int(n))
    ratios.append(numerator/denominator/np.sqrt(n))
plt.figure(figsize=(7.0,3.8))
plt.plot(ns,ratios,'.',markersize=1.2,label='Exact ratio formula')
plt.plot(ns,np.sqrt(2)+2.5/np.sqrt(ns),'--',linewidth=1,label='Leading envelopes')
plt.plot(ns,np.sqrt(2)-0.5/np.sqrt(ns),'--',linewidth=1)
plt.axhline(np.sqrt(2),linewidth=0.9,label=r'$\sqrt{2}$')
plt.xlabel(r'$n$')
plt.ylabel(r'$a(n+1)/(a(n)\sqrt{n})$')
plt.legend(fontsize=8)
save_figure('ratio_convergence')

# Figure 2: the first lattice-dependent correction.
phase,scaled=[] ,[]
for n in range(1000,16001,19):
    la,ll,delta=log_values(n,60)
    phase.append(float(delta))
    scaled.append(float(mp.sqrt(2*n)*(la-ll)))
grid=np.linspace(-2,2,401)
plt.figure(figsize=(7.0,3.8))
plt.plot(phase,scaled,'.',markersize=2.3,label=r'$\sqrt{2n}\log(a(n)/L(n))$')
plt.plot(grid,41/24-grid*grid/2,linewidth=1.4,label=r'$41/24-\delta^2/2$')
plt.xlabel(r'$\delta_n=d_n-\sqrt{2n}+3/2$')
plt.ylabel('Scaled logarithmic correction')
plt.legend(fontsize=8)
save_figure('lattice_correction')

# Figure 3: successive correction orders. Values are calculated with
# log-gamma and expm1 at high precision, not from subtracting huge integers.
ns=sorted(set(int(round(x)) for x in np.geomspace(100,10**9,220)))
errors=[[],[],[],[]]
for n in ns:
    la,ll,delta=log_values(n,70)
    s=mp.sqrt(2*n)
    p=correction_polynomials(delta)
    residual=la-ll
    errors[0].append(float(abs(mp.expm1(residual))))
    for i in range(3):
        residual-=p[i]/s**(i+1)
        errors[i+1].append(float(abs(mp.expm1(residual))))
plt.figure(figsize=(7.0,3.8))
for values,label in zip(errors,[r'$L$',r'$L_1$',r'$L_2$',r'$L_3$']):
    plt.loglog(ns,values,linewidth=1,label=label)
plt.xlabel(r'$n$')
plt.ylabel('Absolute relative error')
plt.legend(fontsize=9,ncol=4)
save_figure('approximation_errors')

print('Generated numerical table, computed terms 0..1000, and three figures.')
for row in rows:
    print(row[:2], 'a/L=',row[3], 'first corrected error=',row[4])
