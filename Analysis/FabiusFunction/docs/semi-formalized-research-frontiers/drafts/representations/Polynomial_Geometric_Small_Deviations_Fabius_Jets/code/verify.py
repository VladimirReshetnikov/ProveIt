#!/usr/bin/env python3
"""Reproducible diagnostics for polynomial--geometric small deviations.

These computations check formulas; they are NOT interval-arithmetic proofs.
The mathematical remainder proofs are in article.tex. Run from package root:
    python code/verify.py --output results
Dependencies: mpmath, numpy, scipy, sympy. No network or random input is used.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from pathlib import Path
from typing import Callable
import mpmath as mp
import numpy as np
import scipy
from scipy.integrate import quad
import sympy as sp


def boundary_data(s: mp.mpf, lam: mp.mpf, digits: int = 60) -> dict:
    """C_0 and its first four w-derivatives, plus weighted derivative sums."""
    if lam <= 0:
        raise ValueError("lambda must be positive")
    with mp.workdps(digits + 35):
        cutoff = (digits + 12) * mp.log(10)
        kmax = int(mp.ceil(cutoff / lam)) + 3
        C = mp.mpf(0)
        derivatives = [mp.mpf(0) for _ in range(4)]
        weighted = [mp.mpf(0) for _ in range(3)]
        weighted2 = [mp.mpf(0), mp.mpf(0)]
        for k in range(-kmax, kmax + 1):
            u = mp.mpf(k) - s
            z = mp.exp(-lam * u)
            if k <= 0 and z > cutoff + 30:
                continue  # error much smaller than requested working accuracy
            ez = mp.exp(z)
            den = mp.expm1(z)
            C += mp.log1p(-mp.exp(-z)) if k <= 0 else mp.log(-mp.expm1(-z) / z)
            ds = [z / den,
                  -z*z*ez / den**2,
                  z**3*ez*(ez+1) / den**3,
                  -z**4*ez*(ez**2+4*ez+1) / den**4]
            if k >= 1:
                ds = [v + (-1)**j * mp.factorial(j-1)
                      for j, v in enumerate(ds, 1)]
            for j, v in enumerate(ds):
                derivatives[j] += v
                if j < 3:
                    weighted[j] += u * v
                if j < 2:
                    weighted2[j] += u*u * v
        a, b, c, d = derivatives
        psi = lam * (s-s*s) / 2 - C
        return dict(C=C, derivatives=derivatives, weighted=weighted,
                    weighted2=weighted2, psi=psi,
                    psi1=lam*(mp.mpf('0.5')-s-a),
                    psi2=-lam-lam*lam*(a+b),
                    psi_lambda=(s-s*s)/2+weighted[0])


def fourier_psi(s: mp.mpf, lam: mp.mpf, digits: int = 60) -> mp.mpf:
    with mp.workdps(digits + 15):
        cstar = mp.pi**2/12 - mp.euler**2/2 - mp.stieltjes(1)
        value = lam/12 + cstar/lam
        modes = int(mp.ceil((digits+12)*mp.log(10)*lam/mp.pi**2))+5
        for k in range(1, modes + 1):
            omega = 2*mp.pi*k/lam
            # Explicit Euler--Maclaurin avoids cancellation in eta-based
            # evaluation at frequencies commensurate with log(2).
            zeta = mp.zeta(1-1j*omega, method='euler-maclaurin')
            value += 2*mp.re(mp.gamma(-1j*omega)*zeta/lam
                             * mp.exp(2j*mp.pi*k*s))
        return +value


def coefficients(m: mp.mpf, lam: mp.mpf, s: mp.mpf, data: dict) -> tuple:
    """A_1 in closed form, and A_2 from the finite extraction formula."""
    p = m+1
    a, b, c, d = data['derivatives']
    w0, w1, w2 = data['weighted']
    u0, u1 = data['weighted2']
    q2 = b+a*a
    q3 = c+3*a*b+a**3
    q4 = d+4*a*c+3*b*b+6*a*a*b+a**4
    C1 = m*w0
    C1w = m*(w0+w1)
    C1ww = m*(2*w1+w2)
    C2 = ((m*m-m)*u0+m*m*u1)/2
    bracket1 = C1-s*a-q2/2
    bracket2 = (C2+C1*C1/2-s*(C1w+a*C1)
                -(C1ww+2*a*C1w+q2*C1)/2
                +(s*s+s)*q2/2+(3*s+2)*q3/6+q4/8)
    B2 = s*s-s+mp.mpf(1)/6
    B3 = s**3-mp.mpf('1.5')*s*s+s/2
    t1 = -p*B2/2
    t2 = -p*B3/6+t1*t1/2
    A1raw = t1+bracket1
    A1 = ((1-2*m)/24+1/(2*lam)+m*data['psi_lambda']
          +(data['psi2']-data['psi1']**2)/(2*lam*lam))
    assert abs(A1-A1raw) < mp.mpf('1e-50')
    return A1, bracket2+t1*bracket1+t2


def normalized_cdf(m: mp.mpf, lam: mp.mpf, R: mp.mpf, psi: mp.mpf,
                   eta: Callable[[int], float] | None = None,
                   vmax: float = 20.0) -> tuple[mp.mpf, float]:
    """F(x(R))/leading term, by a scaled, truncated Bromwich integral.

    Double-precision adaptive quadrature is deliberately independent of the
    asymptotic coefficient computation. Returned error is only QUADPACK's
    local estimate; it excludes roundoff and discarded tails.
    """
    if R < 30 or lam <= 0 or m < 0:
        raise ValueError("diagnostic integrator requires R>=30, lambda>0, m>=0")
    n0 = int(mp.floor(R)); s = R-n0
    r, l, mf = float(R), float(lam), float(m)
    late = int(math.ceil(85/l))+20
    z_values, early = [], []
    eta_sum = mp.mpf(0)
    for n in range(1, n0+late):
        shift = 0.0 if eta is None else float(eta(n))
        if n <= n0:
            eta_sum += mp.mpf(shift)
        logz = mf*math.log(n/r)+l*(r-n)+shift
        if n <= n0 and logz > math.log(100):
            continue
        z_values.append(math.exp(logz)); early.append(n <= n0)
    z_values = np.array(z_values)
    early = np.array(early, dtype=bool)
    def amplitude(w: complex) -> complex:
        terms = -np.expm1(-w*z_values)
        terms[~early] /= w*z_values[~early]
        return complex(np.prod(terms))
    def integrand(v: float) -> float:
        u = v/math.sqrt(r)
        kernel = np.exp(1j*u*r-(n0+1)*np.log1p(1j*u))
        return float((kernel*amplitude(1+1j*u)).real)
    integral, err = quad(integrand, 0.0, vmax, epsabs=2e-13,
                         epsrel=2e-13, limit=200)
    if integral <= 0:
        raise ArithmeticError("nonpositive quadrature; raise precision or revise contour")
    norm = mp.exp(R+mp.loggamma(n0+1)-n0*mp.log(R))/(mp.pi*mp.sqrt(R))
    J = mp.mpf(integral)*norm
    stirling_residual = (n0*mp.log(R)-mp.loggamma(n0+1)-R
                         +mp.log(2*mp.pi*R)/2)
    logratio = (-lam*(s-s*s)/2+(m+1)*stirling_residual+psi
                +mp.log(J)-eta_sum)
    return mp.exp(logratio), err


def symbolic_checks() -> dict:
    e, s, m, l, v, w, z = sp.symbols('e s m l v w z')
    a = sp.Rational(1,2)-s-v/l
    b = -1/l-w/l**2-a
    C1 = -m*((s-s*s)/2-z)
    raw = -(m+1)*sp.bernoulli(2,s)/2+C1-s*a-(b+a*a)/2
    claimed = (1-2*m)/24+1/(2*l)+m*z+(w-v*v)/(2*l*l)
    assert sp.simplify(raw-claimed) == 0
    # At order r, the Gamma reference moment has degree at most 2r in z.
    for j in range(1, 11):
        poly = sp.expand(sum(sp.binomial(j,k)*(-1)**(j-k)
                      *sp.prod(1-(s+a0)*e for a0 in range(k))
                      for k in range(j+1)))
        for r in range((j+1)//2):
            assert sp.expand(poly).coeff(e,r) == 0
    return {'first_coefficient_identity': True,
            'gamma_moment_vanishing_through_j': 10}


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open('w', newline='', encoding='utf-8') as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results'))
    parser.add_argument('--digits', type=int, default=60)
    args = parser.parse_args()
    if args.digits < 60:
        parser.error('--digits must be at least 60')
    args.output.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.digits
    symbolic = symbolic_checks()
    periodic = []
    for name, lam in [('log2',mp.log(2)),('1',mp.mpf(1)),('2',mp.mpf(2))]:
        for ss in ['0','.37','.91']:
            s = mp.mpf(ss); data = boundary_data(s,lam,args.digits)
            error = abs(data['psi']-fourier_psi(s,lam,args.digits))
            assert error < mp.mpf('1e-50')
            periodic.append(dict(lam=name, phase=ss, psi=mp.nstr(data['psi'],35),
                                 product_fourier_difference=mp.nstr(error,8)))
    rows = []
    for mi, name, lam in [(0,'log2',mp.log(2)),(1,'log2',mp.log(2)),
                         (3,'2',mp.mpf(2)),(0,'2',mp.mpf(2))]:
        m=mp.mpf(mi); s=mp.mpf('.37'); data=boundary_data(s,lam,args.digits)
        A1,A2=coefficients(m,lam,s,data)
        for n in [40,80,160,320]:
            R=n+s; ratio,err=normalized_cdf(m,lam,R,data['psi'])
            alt,_=normalized_cdf(m,lam,R,data['psi'],vmax=24.0)
            row=dict(m=mi,lam=name,R=mp.nstr(R,10),
                     A1=mp.nstr(A1,18),A2=mp.nstr(A2,18),
                     ratio_to_leading=mp.nstr(ratio,18),
                     R_times_error0=mp.nstr(R*(ratio-1),14),
                     R2_times_error1=mp.nstr(R**2*(ratio-1-A1/R),14),
                     R3_times_error2=mp.nstr(R**3*(ratio-1-A1/R-A2/R**2),14),
                     contour_cutoff_change=mp.nstr(abs(ratio-alt),8),
                     quadrature_estimate=err)
            rows.append(row)
            print(json.dumps(row), flush=True)
    comparison=[]
    m=mp.mpf(1); lam=mp.log(2); s=mp.mpf('.37'); c=mp.mpf('.7')
    data=boundary_data(s,lam,args.digits)
    for n in [40,80,160,320]:
        R=n+s
        base,_=normalized_cdf(m,lam,R,data['psi'])
        changed,_=normalized_cdf(m,lam,R,data['psi'],eta=lambda j:float(c/j))
        partial=mp.fsum(mp.mpf(float(c/j)) for j in range(1,n+1))
        comparison.append(dict(R=mp.nstr(R,10),
                         renormalized_ratio=mp.nstr(changed/base*mp.exp(partial),18),
                         harmonic_scaled_ratio=mp.nstr(changed/base*R**c*mp.exp(c*mp.euler),18)))
    write_csv(args.output/'periodic.csv',periodic)
    write_csv(args.output/'asymptotics.csv',rows)
    write_csv(args.output/'comparison.csv',comparison)
    metadata=dict(python=platform.python_version(),mpmath=mp.__version__,
                  numpy=np.__version__,scipy=scipy.__version__,sympy=sp.__version__,
                  digits=args.digits,symbolic=symbolic,
                  numerical_status='diagnostics, not interval certificates',
                  max_product_fourier_difference=max(float(r['product_fourier_difference']) for r in periodic),
                  max_cutoff_change=max(float(r['contour_cutoff_change']) for r in rows))
    (args.output/'verification.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))

if __name__ == '__main__':
    main()
