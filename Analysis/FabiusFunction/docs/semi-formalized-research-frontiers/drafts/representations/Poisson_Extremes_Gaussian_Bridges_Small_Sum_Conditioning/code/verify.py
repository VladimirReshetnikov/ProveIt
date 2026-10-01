#!/usr/bin/env python3
"""Reproduce diagnostics for polynomial uniform-series extremes.

The proofs are in article.tex. These floating-point calculations are NOT
interval certificates. No Monte Carlo truncation is presented as an exact law.
The infinite tail in Fourier inversion is evaluated using its convergent
Bernoulli--Hurwitz-zeta series; changing the tail order, head length, and
integration cutoff is a numerical stability check, not a rounding-error proof.
ed. (2026-09-30): results go to data-rerun/ unless --output is given (the
recorded data/ files are not overwritten by default, not even by --quick),
and both files are written with LF line endings on every platform.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from pathlib import Path
from typing import Any
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gamma, gammaincc, zeta
import sympy as sp


def bernoulli_coefficients(order: int) -> list[tuple[int, float]]:
    return [(r, float(sp.bernoulli(r) / (r * sp.factorial(r))))
            for r in range(2, order + 1, 2)]


def moments(a: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Stable mean and variance of density exp(-y)/(1-exp(-a)), 0<y<a."""
    a = np.asarray(a, dtype=float)
    if np.any(a <= 0):
        raise ValueError('Caps must be positive.')
    m = np.empty_like(a)
    v = np.empty_like(a)
    small = a < 0.1
    x = a[small]
    m[small] = x / 2
    v[small] = 0
    for r, c in bernoulli_coefficients(16):
        m[small] -= r * c * x ** r
        v[small] += r * (r - 1) * c * x ** r
    x = a[~small]
    e = np.exp(-x)
    d = -np.expm1(-x)
    m[~small] = 1 - x * e / d
    v[~small] = 1 - x * x * e / (d * d)
    return m, v


class TiltedSeries:
    def __init__(self, p: float, N: float, head_factor: float = 4., order: int = 16):
        if not p > 1 or N <= 1 or head_factor < 2 or order < 4 or order % 2:
            raise ValueError('Require p>1, N>1, head_factor>=2, even order>=4.')
        self.p, self.N = p, N
        self.J = math.ceil(head_factor * N)
        self.a = (N / np.arange(1, self.J + 1)) ** p
        self.m, self.v = moments(self.a)
        self.coef = bernoulli_coefficients(order)
        # sum_{j>J} a_j^r, evaluated via Hurwitz zeta.
        self.tail = [(r, c, N ** (p*r) * zeta(p*r, self.J+1))
                     for r, c in self.coef]
        first = N ** p * zeta(p, self.J+1)
        self.mean = float(self.m.sum() + first/2 - sum(r*c*h for r,c,h in self.tail))
        self.var = float(self.v.sum() + sum(r*(r-1)*c*h for r,c,h in self.tail))
        self.b = brentq(lambda b: b + math.log(b)/p - math.log(N),
                        1e-10, math.log(N)+1)

    def normalization(self, cap: float | None = None, cutoff: float = 30.) -> float:
        """Compute E_Q[exp(T-mu) 1(T<=mu)] after optional max-capping.

        With cap, the expectation is under Q(. | all Y_j<=cap), still
        centered at the ORIGINAL mean mu. The exact mathematical expression
        is Fourier inversion; this method evaluates it numerically.
        """
        a = self.a if cap is None else np.minimum(self.a, cap)
        if cap is not None and cap <= self.a[-1]:
            raise ValueError('Cap intersects the zeta tail; increase head_factor.')
        m, _ = moments(a)
        delta = float((self.m - m).sum())
        logd = np.log(-np.expm1(-a))
        sum_m = float(m.sum())
        sqrtV = math.sqrt(self.var)
        tail_radius = (self.N/(self.J+1))**self.p * math.hypot(1., cutoff/sqrtV)
        if tail_radius >= 2*math.pi:
            raise ValueError('Tail expansion is outside its convergence disk; increase head_factor.')

        def integrand(u: float) -> float:
            s = u/sqrtV
            lc = np.sum(np.log(-np.expm1(-a*(1-1j*s))) - logd)
            lc -= self.J*np.log1p(-1j*s) + 1j*s*sum_m
            for r, c, h in self.tail:
                lc += c*h*(np.expm1(r*np.log1p(-1j*s)) + 1j*r*s)
            lc -= 1j*s*delta
            return float(np.real(np.exp(lc)/(1-1j*s)))
        val, err = quad(integrand, 0, cutoff, epsabs=3e-11, epsrel=3e-11, limit=250)
        return val/(math.pi*sqrtV)

    def log_tilted_cdf(self, y: float) -> float:
        if y <= 0:
            return -math.inf
        count = math.floor(self.N*y**(-1/self.p))
        if count == 0:
            return 0.
        a = (self.N/np.arange(1, count+1))**self.p
        return float(count*np.log(-np.expm1(-y)) - np.log(-np.expm1(-a)).sum())


def symbolic_checks() -> dict[str, bool]:
    beta, z, h, a = sp.symbols('beta z h a', positive=True)
    checks: dict[str, bool] = {}
    m = 1-a/(sp.exp(a)-1)
    v = 1-a*a*sp.exp(a)/(sp.exp(a)-1)**2
    checks['variance_equals_m_minus_a_mprime'] = sp.simplify(v-(m-a*sp.diff(m,a))) == 0
    for k in range(5):
        left = sum((-1)**j*sp.rf(beta,j)*h**j*(1+z*h)**(-beta-j)
                   for j in range(k+1))
        coeff = sp.expand(sp.series(left,h,0,k+1).removeO()).coeff(h,k)
        expect = (-1)**k*sp.rf(beta,k)*sum(z**j/sp.factorial(j) for j in range(k+1))
        checks[f'gamma_log_cdf_coefficient_{k}'] = sp.simplify(coeff-expect)==0
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    # ed. (2026-09-30): the default leaves the recorded data/ files untouched.
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data-rerun',
                        help='output directory (default: data-rerun; pass data to '
                             'overwrite the recorded files)')
    parser.add_argument('--quick', action='store_true', help='Skip the larger N and stability rerun.')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    checks = symbolic_checks()
    if not all(checks.values()):
        raise RuntimeError(f'Symbolic check failed: {checks}')
    rows: list[dict[str, Any]] = []
    Ns = [32,128,512] if args.quick else [32,128,512,2048]
    for N in Ns:
        model = TiltedSeries(2., float(N))
        D = model.normalization()
        for z0 in [-1.,0.,1.]:
            y = model.b + z0
            logQ = model.log_tilted_cdf(y)
            Dy = model.normalization(y)
            cond = math.exp(logQ)*Dy/D
            intensity = N*gamma(0.5)*gammaincc(0.5,y)
            b = model.b
            correction2 = -math.exp(-z0)*(1-0.5*(z0+1)/b
                               +0.75*(z0*z0/2+z0+1)/(b*b))
            row = dict(p=2.,N=N,z=z0,b=b,mu=model.mean,V=model.var,
                       saddle_ratio=D*math.sqrt(2*math.pi*model.var),
                       tilted_cdf=math.exp(logQ),conditioned_cdf=cond,
                       gamma_cdf=math.exp(-intensity),gumbel_cdf=math.exp(-math.exp(-z0)),
                       order2_cdf=math.exp(correction2),conditioning_ratio=Dy/D,
                       intensity=intensity,
                       lattice_error=abs(logQ+intensity), e_minus_y=math.exp(-y))
            rows.append(row)
            print(f'N={N:4d} z={z0:+.0f}  P={cond:.10f} Q={math.exp(logQ):.10f}'
                  f' gamma={math.exp(-intensity):.10f} D_y/D={Dy/D:.10f}',flush=True)
    stability = {}
    if not args.quick:
        base = next(r for r in rows if r['N']==128 and r['z']==0)
        alt = TiltedSeries(2.,128.,head_factor=6.,order=20)
        Da = alt.normalization(cutoff=36.)
        Dya = alt.normalization(alt.b,cutoff=36.)
        cdfa = math.exp(alt.log_tilted_cdf(alt.b))*Dya/Da
        stability = {'N':128,'z':0,'head_factor':6,'tail_order':20,'cutoff':36,
                     'absolute_cdf_change':abs(cdfa-base['conditioned_cdf']),
                     'absolute_mean_change':abs(alt.mean-base['mu']),
                     'absolute_variance_change':abs(alt.var-base['V'])}
    with (args.output/'maximum_table.csv').open('w',newline='') as f:
        # ed. (2026-09-30): lineterminator='\n' (the csv default is CRLF on every platform).
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n')
        writer.writeheader();writer.writerows(rows)
    # Integral constants independently checked against gamma-zeta formula.
    import mpmath as mp
    mp.mp.dps=45
    beta=mp.mpf('0.5')
    C=-mp.gamma(1-beta)*mp.zeta(1-beta)
    # Stable a-coordinate integral for A=beta int m(a) a^{-beta-1} da.
    def mm(a):
        if abs(a)<mp.mpf('1e-15'):
            return a/2-a*a/12+a**4/720
        return 1-a/mp.expm1(a)
    Aint=beta*mp.quad(lambda a:mm(a)*a**(-beta-1),[0,1,mp.inf])
    constants={'p':2,'C':str(C),'A':str(beta*C),'B':str((1-beta)*beta*C),
               'A_integral':str(Aint),'A_integral_discrepancy':str(abs(Aint-beta*C))}
    report={'status':'floating-point diagnostics; not interval or Lean certificates',
            'versions':{'python':platform.python_version(),'numpy':np.__version__,
                        'scipy':scipy.__version__,'sympy':sp.__version__,'mpmath':mp.__version__},
            'symbolic_checks':checks,'row_count':len(rows),'stability':stability,
            'constants':constants}
    # ed. (2026-09-30): newline='\n' so the JSON is LF on Windows too.
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
