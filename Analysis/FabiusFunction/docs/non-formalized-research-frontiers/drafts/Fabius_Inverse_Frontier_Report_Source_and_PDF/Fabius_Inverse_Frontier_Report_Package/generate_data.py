from __future__ import annotations

from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import csv
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path('/mnt/data/fabius_inverse_frontier')
FIG = ROOT / 'figures'
DATA = ROOT / 'data'
FIG.mkdir(parents=True, exist_ok=True)
DATA.mkdir(parents=True, exist_ok=True)

mp.mp.dps = 100
L = mp.log(2)
B = 1 + L/2
beta = B/L
Csharp = (6*mp.euler**2 + 12*mp.stieltjes(1) - mp.pi**2)/(12*L) - 7*L/12 - mp.log(mp.pi)/2
kappa0 = 1/(2*L) - L/8 - Csharp


def half_moments(N: int) -> list[Fraction]:
    d = [Fraction(1, 1)]
    for n in range(1, N + 1):
        numerator = sum(Fraction(comb(n + 1, k), 1) * d[k] for k in range(n))
        d.append(numerator / ((n + 1) * (2**n - 1)))
    return d


def ffrac(x: Fraction) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator

D = half_moments(120)


def inverse_dyadic_value(n: int) -> Fraction:
    return D[n] / (factorial(n) * 2**(n*(n-1)//2))


def psi_hat(k: int) -> mp.mpc:
    chi = 2*mp.pi*1j*k/L
    return -mp.gamma(-chi)*mp.zeta(1-chi)/L

COEFF = [None] + [psi_hat(k) for k in range(1, 10)]


def psi_values(u: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    p0 = mp.mpc(0)
    p1 = mp.mpc(0)
    p2 = mp.mpc(0)
    for k in range(1, len(COEFF)):
        c = COEFF[k]
        e = mp.e**(2*mp.pi*1j*k*u)
        t0 = c*e
        t1 = (2*mp.pi*1j*k)*t0
        t2 = (2*mp.pi*1j*k)**2*t0
        p0 += t0 + mp.conj(t0)
        p1 += t1 + mp.conj(t1)
        p2 += t2 + mp.conj(t2)
    return mp.re(p0), mp.re(p1), mp.re(p2)


def endpoint_row(n: int) -> dict[str, mp.mpf | int]:
    y = inverse_dyadic_value(n)
    T = -mp.log(ffrac(y))
    rho = mp.sqrt(2*T/L)
    theta = rho + beta
    psi, psip, psipp = psi_values(theta)
    A1 = mp.mpf(1)/24 + 1/(2*L) - (psipp + psip**2)/(2*L**2)
    d1 = beta**2/2 + (Csharp + psi - mp.log(rho)/2)/L
    d2 = (psip*d1 + A1 - beta/2)/L
    h1 = beta - L*d1
    h2 = d1 - beta**2/2 - L*d2
    G0 = rho * mp.e**(-L*rho-L*beta)
    G1 = G0 * mp.e**(h1/rho)
    G2 = G0 * mp.e**(h1/rho + h2/rho**2)
    actual = mp.power(2, -n)
    return {
        'n': n, 'T': T, 'rho': rho, 'theta_mod_1': mp.frac(theta),
        'psi': psi, 'actual': actual,
        'G0': G0, 'G1': G1, 'G2': G2,
        'rel0': G0/actual-1, 'rel1': G1/actual-1, 'rel2': G2/actual-1,
    }

rows = [endpoint_row(n) for n in range(5, 121)]
with (DATA / 'endpoint_errors.csv').open('w', newline='') as fh:
    w = csv.writer(fh)
    w.writerow(rows[0].keys())
    for row in rows:
        w.writerow([mp.nstr(row[k], 45) if k != 'n' else row[k] for k in row])

# Endpoint convergence plot.
fig = plt.figure(figsize=(7.2, 4.5))
ax = fig.add_subplot(111)
ns = [r['n'] for r in rows]
ax.semilogy(ns, [float(abs(r['rel0'])) for r in rows], label='leading equivalent')
ax.semilogy(ns, [float(abs(r['rel1'])) for r in rows], label='first inverse correction')
ax.semilogy(ns, [float(abs(r['rel2'])) for r in rows], label='second inverse correction')
ax.set_xlabel('inverse-dyadic index n')
ax.set_ylabel('absolute relative error at y = F(2^{-n})')
ax.grid(True, which='both', alpha=0.3)
ax.legend()
fig.tight_layout()
fig.savefig(FIG / 'endpoint_inverse_errors.png', dpi=220)
plt.close(fig)

# Periodic fluctuation plot, scaled for visibility.
us = [i/2000 for i in range(2001)]
ps = [float(1e6*psi_values(mp.mpf(i)/2000)[0]) for i in range(2001)]
fig = plt.figure(figsize=(7.2, 4.0))
ax = fig.add_subplot(111)
ax.plot(us, ps)
ax.set_xlabel('phase u')
ax.set_ylabel(r'$10^6\,\Psi(u)$')
ax.grid(True, alpha=0.3)
fig.tight_layout()
fig.savefig(FIG / 'periodic_inverse_phase.png', dpi=220)
plt.close(fig)

# Exact r=2 quantile germ and q-Richardson errors.
def delta2(Q: mp.mpf) -> mp.mpf:
    return (mp.sqrt(1 + mp.mpf(64)*Q/9) - 1)/8


def qweights(s: int) -> list[Fraction]:
    q = Fraction(1, 4)
    out: list[Fraction] = []
    for j in range(s):
        num = Fraction(1, 1)
        den = Fraction(1, 1)
        for ell in range(s):
            if ell == j:
                continue
            num *= -q**ell
            den *= q**j - q**ell
        out.append(num/den)
    return out


def G2(n: int) -> mp.mpf:
    return mp.mpf(1)/4 + delta2(mp.power(4, -n))


def extrap(n: int, s: int) -> mp.mpf:
    return sum(ffrac(w)*G2(n+j) for j, w in enumerate(qweights(s)))

qrows = []
for n in range(3, 17):
    raw = G2(n)-mp.mpf(1)/4
    e2 = extrap(n, 2)-mp.mpf(1)/4
    e3 = extrap(n, 3)-mp.mpf(1)/4
    qrows.append({
        'n': n, 'raw': raw, 'R2': e2, 'R3': e3,
        'raw_ratio': raw / (mp.mpf(4)/9*mp.power(4, -n)),
        'R2_ratio': e2 / (mp.mpf(16)/81*mp.power(16, -n)),
        'R3_ratio': e3 / (mp.mpf(32)/729*mp.power(64, -n)),
    })
with (DATA / 'quarter_quantile_errors.csv').open('w', newline='') as fh:
    w = csv.writer(fh)
    w.writerow(qrows[0].keys())
    for row in qrows:
        w.writerow([row['n'] if k == 'n' else mp.nstr(row[k], 45) for k in row])

fig = plt.figure(figsize=(7.2, 4.5))
ax = fig.add_subplot(111)
ax.semilogy([r['n'] for r in qrows], [float(abs(r['raw'])) for r in qrows], marker='o', label='raw finite-prefix inverse')
ax.semilogy([r['n'] for r in qrows], [float(abs(r['R2'])) for r in qrows], marker='s', label='two-level q-Richardson')
ax.semilogy([r['n'] for r in qrows], [float(abs(r['R3'])) for r in qrows], marker='^', label='three-level q-Richardson')
ax.set_xlabel('prefix depth n')
ax.set_ylabel(r'absolute error at $y=F(1/4)=5/72$')
ax.grid(True, which='both', alpha=0.3)
ax.legend()
fig.tight_layout()
fig.savefig(FIG / 'quarter_quantile_richardson.png', dpi=220)
plt.close(fig)

# Constants and selected rows for direct LaTeX inclusion.
with (DATA / 'constants.txt').open('w') as fh:
    fh.write(f'L={mp.nstr(L,50)}\n')
    fh.write(f'beta={mp.nstr(beta,50)}\n')
    fh.write(f'Csharp={mp.nstr(Csharp,50)}\n')
    fh.write(f'kappa0={mp.nstr(kappa0,50)}\n')
    grid = [(psi_values(mp.mpf(i)/10000)[0], mp.mpf(i)/10000) for i in range(10001)]
    mn = min(grid, key=lambda t: t[0])
    mx = max(grid, key=lambda t: t[0])
    fh.write(f'psi_min~={mp.nstr(mn[0],35)} at {mp.nstr(mn[1],12)}\n')
    fh.write(f'psi_max~={mp.nstr(mx[0],35)} at {mp.nstr(mx[1],12)}\n')

print('Generated data and figures in', ROOT)
