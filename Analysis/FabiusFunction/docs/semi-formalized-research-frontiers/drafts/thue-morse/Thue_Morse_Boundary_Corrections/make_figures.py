#!/usr/bin/env python3
"""Reproduce the illustrative figures and Poisson table.

Optional dependencies: matplotlib, numpy, mpmath. Unlike verify.py, this script
uses high-precision floating point. It checks the displayed errors against an
independent evaluation of finite Laurent polynomials. No numerical integration
of increasingly spiky densities is used.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import numpy as np
import matplotlib.pyplot as plt
import mpmath as mp
from verify import eta, multiply_riesz, partition_coefficients

ROOT = Path(__file__).resolve().parent
FIG = ROOT / 'figures'
FIG.mkdir(exist_ok=True)
mp.mp.dps = 160
rho = mp.mpf(4) / 5
cutoff = 2200
p = partition_coefficients(cutoff)
kappa = [F(1)]
for n in range(1, cutoff+1):
    kappa.append(F(3*p[n],2) - (kappa[n//2]/2 if n%2==0 else F(0)))

def as_mp(value):
    return mp.mpf(value.numerator)/value.denominator

km = [as_mp(value) for value in kappa]

def K(t):
    return mp.polyval(list(reversed(km)), t)

E = mp.mpf(1)
t = rho
while t > mp.mpf('1e-170'):
    E *= 1-t
    t *= t
Q = rho*E**2
h = sum(as_mp(eta(k))*rho**k for k in range(cutoff+1))
poisson_limit = 2*h-1
coeff = {0:F(1)}
rows = []
for m in range(10):
    N = 2**m
    nxt = multiply_riesz(coeff, N, F(1))
    raw = 2*sum(as_mp(v)*rho**k for k,v in coeff.items() if k >= 0)-1
    next_value = 2*sum(as_mp(v)*rho**k for k,v in nxt.items() if k >= 0)-1
    corrected = (raw+2*next_value)/3
    t = rho**N
    sign = (-1)**m
    raw_error = sign*2*Q*K(t)/(3*N)
    corrected_error = sign*2*Q*(K(t)-K(t*t))/(9*N)
    assert mp.almosteq(raw-poisson_limit, raw_error, rel_eps=mp.mpf('1e-95'), abs_eps=mp.mpf('1e-145'))
    assert mp.almosteq(corrected-poisson_limit, corrected_error, rel_eps=mp.mpf('1e-95'), abs_eps=mp.mpf('1e-145'))
    rows.append({'m':m, 'N':N, 'raw_error':mp.nstr(abs(raw_error),18),
                 'corrected_error':mp.nstr(abs(corrected_error),18),
                 'ratio':mp.nstr(abs(corrected_error/raw_error),18)})
    coeff = nxt
(ROOT/'poisson_data.json').write_text(json.dumps({'rho':'4/5','precision_digits':160,
    'series_cutoff':cutoff,'limit':mp.nstr(poisson_limit,80),'rows':rows},indent=2)+'\n')

def tex_sci(s):
    number=mp.mpf(s)
    exponent=int(mp.floor(mp.log10(number)))
    mantissa=number/mp.power(10,exponent)
    return r'\({}\times10^{{{}}}\)'.format(mp.nstr(mantissa,5),exponent)
lines=[r'\begin{tabular}{rrrr}',r'\toprule',
       r'$m$ & $N$ & Raw absolute error & Corrected absolute error \\',r'\midrule']
for row in rows:
    cells = [str(row['m']), str(row['N']), tex_sci(row['raw_error']), tex_sci(row['corrected_error'])]
    lines.append(' & '.join(cells) + ' ' + chr(92)*2)
lines += [r'\bottomrule',r'\end{tabular}']
(ROOT/'poisson_table.tex').write_text('\n'.join(lines)+'\n')

fig, ax = plt.subplots(figsize=(6.7,3.9))
ax.semilogy([r['N'] for r in rows],[float(r['raw_error']) for r in rows],'o-',label='Raw Riesz product')
ax.semilogy([r['N'] for r in rows],[float(r['corrected_error']) for r in rows],'s-',label='Positive two-level correction')
ax.set_xlabel('Block length N = 2^m')
ax.set_ylabel('Absolute error for the Poisson observable')
ax.legend(frameon=False)
ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(FIG/'poisson_convergence.pdf')
fig.savefig(FIG/'poisson_convergence.png',dpi=170)
plt.close(fig)

x = np.linspace(0,1,6001)
m = 4
N = 2**m
f = np.ones_like(x)
for j in range(m):
    f *= 1-np.cos(2*np.pi*2**j*x)
corrected = f*(1-2/3*np.cos(2*np.pi*N*x))
fig, ax = plt.subplots(figsize=(6.7,3.6))
ax.plot(x,f,label='f_4 (degree 15)',linewidth=1.0)
ax.plot(x,corrected,label='Corrected f_4 (degree 31)',linewidth=1.0)
ax.set_xlabel('x on the unit circle')
ax.set_ylabel('Nonnegative density')
ax.set_xlim(0,1)
ax.legend(frameon=False)
ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(FIG/'positive_density.pdf')
fig.savefig(FIG/'positive_density.png',dpi=170)
plt.close(fig)
print('Generated two figures and the high-precision Poisson table.')
for row in rows:
    print(row)
