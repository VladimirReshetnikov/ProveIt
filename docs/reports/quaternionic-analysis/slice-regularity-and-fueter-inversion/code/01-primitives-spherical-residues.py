#!/usr/bin/env python3
"""Independent symbolic/numerical checks for Global Fueter Primitives.

Run: python verify_results.py
Dependencies: Python 3.10+, numpy, sympy.
These checks are sanity tests, not substitutes for the proofs in the article.
Quaternion arrays use coordinates (1, i, j, k), with right coefficients.
"""
from __future__ import annotations
import math
import numpy as np
import sympy as sp


def qmul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    a0, av = a[..., :1], a[..., 1:]
    b0, bv = b[..., :1], b[..., 1:]
    return np.concatenate((a0*b0-np.sum(av*bv, axis=-1, keepdims=True),
                           a0*bv+b0*av+np.cross(av, bv)), axis=-1)


def qconj(a: np.ndarray) -> np.ndarray:
    a = np.array(a, dtype=float, copy=True)
    a[..., 1:] *= -1
    return a


def mode(z: np.ndarray, p: complex, a: np.ndarray,
         b: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return P,Q of the branch-independent mode G_{p;a,b}."""
    z = np.asarray(z, dtype=complex)
    x, r, s, t = z.real, z.imag, p.real, p.imag
    if t <= 0 or np.any(r <= 0) or np.any(z == p):
        raise ValueError('Require Im(p)>0, Im(z)>0 and z!=p.')
    dminus = (x-s)**2 + (r-t)**2
    dplus = (x-s)**2 + (r+t)**2
    v = -(np.log(dminus)-np.log(dplus))/(4*math.pi)
    vx = -(x-s)/(2*math.pi)*(1/dminus-1/dplus)
    vr = -((r-t)/dminus-(r+t)/dplus)/(2*math.pi)
    xa_b = x[..., None]*a+b
    P = -2*(vr+v/r)[..., None]*a - (2*vx/r)[..., None]*xa_b
    Q = -2*vx[..., None]*a+2*(vr/r-v/r**2)[..., None]*xa_b
    return P, Q


def periods(p: complex, a: np.ndarray, b: np.ndarray,
            center: complex, radius: float, n: int = 8192
            ) -> tuple[np.ndarray, np.ndarray]:
    theta = 2*math.pi*np.arange(n)/n
    z = center+radius*np.exp(1j*theta)
    dz = 1j*radius*np.exp(1j*theta)
    P, Q = mode(z, p, a, b)
    x, r, dx, dr = [v[..., None] for v in (z.real, z.imag,
                                           dz.real, dz.imag)]
    omega = (-P*dx+Q*dr)/2
    beta = ((x*P+r*Q)*dx+(r*P-x*Q)*dr)/2
    return 2*math.pi*np.mean(omega, axis=0), 2*math.pi*np.mean(beta, axis=0)


def symbolic_checks() -> None:
    x, r = sp.symbols('x r', real=True, positive=True)
    s, t = sp.Rational(3, 10), sp.Rational(6, 5)
    v = -sp.log(((x-s)**2+(r-t)**2)/((x-s)**2+(r+t)**2))/(4*sp.pi)
    vx, vr = sp.diff(v, x), sp.diff(v, r)
    for a, b in [(1, 0), (0, 1)]:
        P = -2*(vr+v/r)*a - 2*vx/r*(x*a+b)
        Q = -2*vx*a+2*(vr/r-v/r**2)*(x*a+b)
        assert sp.simplify(sp.diff(P, x)-sp.diff(Q, r)-2*Q/r) == 0
        assert sp.simplify(sp.diff(Q, x)+sp.diff(P, r)) == 0
        # Compare the target-derived invariant with the independently
        # differentiated logarithmic stem; only rational functions remain.
        z = x+sp.I*r
        p = s+sp.I*t
        Lprime = (1/(z-p)-1/(z-sp.conjugate(p)))/(2*sp.pi*sp.I)
        Lsecond = (-1/(z-p)**2+1/(z-sp.conjugate(p))**2)/(2*sp.pi*sp.I)
        H = -(P+r*sp.diff(P, r))/2-sp.I*r*sp.diff(P, x)/2
        Hfromstem = 2*Lprime*a+Lsecond*(z*a+b)
        assert sp.simplify(sp.together(H-Hfromstem)) == 0
    print('Exact symbolic Vekua and second-derivative identities: PASS')


def run_checks() -> None:
    symbolic_checks()
    p = 0.3+1.2j
    a = np.array([1., -2., .5, 1.])
    b = np.array([.5, 1., -1., 2.])
    for radius in [.1, .3, .7]:
        aa, bb = periods(p, a, b, p, radius)
        assert np.max(np.abs(aa-a)) < 5e-12
        assert np.max(np.abs(bb-b)) < 5e-12
    aa, bb = periods(p, a, b, p+1., .15)
    assert max(np.linalg.norm(aa), np.linalg.norm(bb)) < 5e-12
    print('Period normalization and a non-linking contour: PASS')

    # A local branch is enough for comparison; its discontinuity disappears
    # under the Fueter map. Here complex coordinates are H_C coordinates.
    theta = 2*math.pi*(np.arange(2000)+.31)/2000
    z = p+.25*np.exp(1j*theta)
    r = z.imag[:, None]
    L = np.log((z-p)/(z-p.conjugate()))/(2j*math.pi)
    Lp = (1/(z-p)-1/(z-p.conjugate()))/(2j*math.pi)
    F = L[:, None]*(z[:, None]*a+b)
    Fp = Lp[:, None]*(z[:, None]*a+b)+L[:, None]*a
    P, Q = mode(z, p, a, b)
    assert np.max(np.abs(P+2*Fp.imag/r)) < 2e-12
    assert np.max(np.abs(Q-2*Fp.real/r+2*F.imag/r**2)) < 2e-12
    print('Branch-free mode versus differentiated local stem: PASS')

    c = p.real*a+b
    residue_sq = float(c@c+p.imag**2*(a@a))
    cross_norm = np.linalg.norm(qmul(b, qconj(a))[1:])
    sup_expected = math.sqrt(residue_sq+2*p.imag*cross_norm)/(math.pi*p.imag)
    trace_expected = 8*residue_sq
    print(f'Noncommuting example: residue norm squared = {residue_sq:.12g}')
    print(f'Predicted rho*sup|g| = {sup_expected:.12g}')
    print(f'Predicted rho*integral_boundary |g|^2 = {trace_expected:.12g}')
    print('rho        sup coefficient       tube trace coefficient')
    for rho in [1e-2, 1e-3, 1e-4, 1e-5]:
        z = p+rho*np.exp(1j*theta)
        P, Q = mode(z, p, a, b)
        axial_sq = np.sum(P*P+Q*Q, axis=-1)
        imag_PQ = qmul(P, qconj(Q))[:, 1:]
        max_sq = axial_sq+2*np.linalg.norm(imag_PQ, axis=-1)
        sup_coefficient = rho*math.sqrt(np.max(max_sq))
        trace_coefficient = 8*math.pi**2*rho**2*np.mean(z.imag**2*axial_sq)
        print(f'{rho:<10.1g} {sup_coefficient:20.12g} {trace_coefficient:24.12g}')
    assert abs(sup_coefficient/sup_expected-1) < 2e-4
    assert abs(trace_coefficient/trace_expected-1) < 2e-6
    print('Critical norm and tube energy asymptotics: PASS')

    # The constrained Laurent pair encodes exactly the two H-valued periods.
    cminus2 = -(p*a+b)/(2j*math.pi)
    cminus1 = a/(2j*math.pi)
    assert np.max(np.abs(cminus1-1j*cminus2.real/p.imag)) < 1e-14
    assert np.max(np.abs(-2*math.pi*cminus2.real/p.imag-a)) < 1e-14
    assert np.max(np.abs(2*math.pi*cminus2.imag
                         +2*math.pi*p.real/p.imag*cminus2.real-b)) < 1e-14
    assert abs(32*math.pi**2*np.vdot(cminus2, cminus2).real
               -trace_expected) < 1e-11
    print('Laurent admissibility, residue recovery and energy coefficient: PASS')

    # The leading exterior term is checked on a non-real ray.
    R = 1000.
    zfar = np.asarray(R*np.exp(.7j))
    Pf, Qf = mode(zfar, p, a, b)
    P0 = 4*p.imag/math.pi*zfar.real/R**4*c
    Q0 = -4*p.imag/math.pi*zfar.imag/R**4*c
    relative_error = np.sqrt(np.sum((Pf-P0)**2+(Qf-Q0)**2)) / np.sqrt(
        np.sum(P0**2+Q0**2))
    assert relative_error < .02
    print(f'Leading exterior moment on a non-real ray: PASS '
          f'(relative error at R=1000: {relative_error:.4g})')

    # Exact spherical mean is recovered by the 6 coordinate imaginary units:
    # the linear I term cancels in antipodal pairs, no approximate quadrature.
    I = np.concatenate((np.zeros((6, 1)), np.r_[np.eye(3), -np.eye(3)]), axis=1)
    P0, Q0 = mode(np.asarray(p+.31), p, a, b)
    values = P0+qmul(I, Q0)
    assert abs(np.mean(np.sum(values*values, axis=1))-(P0@P0+Q0@Q0)) < 1e-12
    print('Spherical norm averaging identity: PASS')
    print('ALL CHECKS PASSED. Numerical tests do not establish priority or prove the theorems.')


if __name__ == '__main__':
    run_checks()
