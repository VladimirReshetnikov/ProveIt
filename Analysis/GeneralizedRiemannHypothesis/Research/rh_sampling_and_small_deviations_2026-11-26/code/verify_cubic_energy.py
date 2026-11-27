#!/usr/bin/env python3
"""Reproduce finite checks and figures for the cubic sampling theorem.

The infinite statements are proved in cubic_sampling.tex. These checks
verify algebraic identities, constants, and a finite part of the explicit
counterexample; they are not a numerical proof of RH or of meromorphy.
"""
from pathlib import Path
import json
import math
import numpy as np
import sympy as sp
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
(ROOT / "checks").mkdir(exist_ok=True)
(ROOT / "figures").mkdir(exist_ok=True)
mp.mp.dps = 60

u, h = sp.symbols("u h", real=True)
phi = u**3 * (1-u)**3
z = u*(1-u)
assert sp.expand(sp.diff(phi,u,2)-6*z*(1-5*z)) == 0
assert sp.integrate(phi, (u,0,1)) == sp.Rational(1,140)
mu = [sp.integrate(u**j*phi,(u,0,1)) for j in range(7)]
assert all(mu[j] == sp.Rational(6,(j+4)*(j+5)*(j+6)*(j+7))
           for j in range(7))
gap_integral = h**2/(1-sp.exp(-h))-h-h**2/2
series = sp.series(gap_integral,h,0,9)
assert sp.expand(series.removeO()).coeff(h,3) == sp.Rational(1,12)
assert sp.expand(series.removeO()).coeff(h,5) == -sp.Rational(1,720)

# The general counterexample has rightmost poles at beta+(2m+1)*pi*i.
beta = 0.65
delta = (1-beta)/3
K = 3
N = 100000

def bump(t):
    t = np.asarray(t,dtype=float)
    k = np.floor(t).astype(int)
    hk = np.exp(-delta*k)
    v = (t-k)/hk
    inside = (k>=K)&(v>0)&(v<1)
    p = np.where(inside, v**3*(1-v)**3, 0.0)
    return np.where(k%2==0,1.,-1.)*hk**2*p

def f(x):
    x = np.asarray(x,dtype=float)
    return x*(np.log(x)+bump(np.log(x)))

grid = np.arange(1,N+2,dtype=float)
F = f(grid)
a = np.empty(N)
a[0] = F[1]
a[1:] = np.arange(2,N+1)*(F[2:]-2*F[1:-1]+F[:-2])
assert np.min(a)>0 and np.max(a)<4

# Reconstruct the hinge sum from its independent coefficients.
n = np.arange(1,N+1,dtype=float)
S = np.cumsum(a/n)-np.cumsum(a)/n
R = S-np.log(n)
r = bump(np.log(n))
reconstruction_error = float(np.max(np.abs(R-r)))
assert reconstruction_error < 1e-8
retained = (r==0)
assert np.max(np.abs(R[retained])) < 1e-8

# Off-grid interpolation correction: compare at fractional locations.
x = np.arange(2,N-1,113,dtype=float)+0.371
j = np.floor(x).astype(int)
IF = F[j-1]+(x-j)*(F[j]-F[j-1])
err = IF/x-np.log(x)-bump(np.log(x))
bound = 25/(64*x*x)
# Floating arithmetic loses a few ulps when subtracting log(x).
assert np.min(err)>-5e-14
assert np.max(err-bound)<5e-14

# Verify the exact Jensen envelope integral with high precision.
quadrature_checks = []
for hs in ["0.01","0.1","0.5","1.0"]:
    hh=mp.mpf(hs)
    J=lambda y: hh*(-mp.expm1(-y))/(-mp.expm1(-hh))-y
    integral=mp.quad(J,[0,hh])
    exact=hh**2/(-mp.expm1(-hh))-hh-hh**2/2
    assert abs(integral-exact)<mp.mpf("1e-55")
    quadrature_checks.append({"h":hs,"integral":mp.nstr(integral,20),
                              "integral_over_h_cubed":mp.nstr(integral/hh**3,20)})

report = {
    "status":"all checks passed",
    "meaning":"Finite algebraic and numerical checks; full proofs are in the paper.",
    "phi_second_derivative":"6 u(1-u) [1-5u(1-u)]",
    "leading_residue":"1/140",
    "gap_integral_series":str(series),
    "construction":{"beta":beta,"delta":delta,"K":K,"N":N,
                    "min_coefficient":float(a.min()),"max_coefficient":float(a.max()),
                    "reconstruction_max_absolute_error":reconstruction_error,
                    "retained_count":int(retained.sum()),
                    "omitted_count":int((~retained).sum())},
    "quadrature_checks":quadrature_checks,
}
(ROOT/"checks"/"cubic_energy_checks.json").write_text(json.dumps(report,indent=2)+"\n")

plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                     "axes.spines.top":False,"axes.spines.right":False,
                     "figure.dpi":150})
fig, ax=plt.subplots(1,2,figsize=(10.7,3.6))
yy=np.linspace(0,1,501)
for hh,col in [(0.02,"#124E78"),(0.5,"#C36E30"),(1.0,"#64843E")]:
    J=hh*(-np.expm1(-hh*yy))/(-np.expm1(-hh))-hh*yy
    ax[0].plot(yy,J/hh**2,label=f"h = {hh:g}",color=col,lw=1.8)
ax[0].plot(yy,yy*(1-yy)/2,"--",color="#555555",lw=1,label="limit y(1-y)/2")
ax[0].set(xlabel="Fraction of logarithmic gap",ylabel="J_h(h y) / h²",
          title="An unobserved interval has quadratic height")
ax[0].legend(frameon=False,fontsize=8)
tt=np.linspace(3,11.8,8000)
rr=bump(tt)
ax[1].plot(tt,rr,color="#124E78",lw=1.6)
ax[1].axhline(0,color="#888888",lw=.7)
for kk in range(K,12):
    ax[1].axvspan(kk,kk+math.exp(-delta*kk),color="#C36E30",alpha=.10)
ax[1].set(xlabel="log x",ylabel="r(log x)",
          title="Hidden alternating bumps; retained readings are zero")
ax[1].text(.03,.93,"Shaded intervals contain omitted samples",
           transform=ax[1].transAxes,fontsize=8,va="top")
fig.tight_layout(pad=1.3)
fig.savefig(ROOT/"figures"/"cubic_mechanism.pdf",bbox_inches="tight")
fig.savefig(ROOT/"figures"/"cubic_mechanism.png",bbox_inches="tight")
plt.close(fig)
print(json.dumps(report,indent=2))
