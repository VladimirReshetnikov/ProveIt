#!/usr/bin/env python3
"""Reproducible checks for fueter_monodromy.tex.

These are consistency checks, not a formal verification of the paper.
The default run requires SymPy. The numerical-only run uses the standard
library: python verify.py --numerical-only.

Conventions: Python's 1j represents the CENTRAL complex unit iota, not a
quaternionic imaginary unit. Scalar kernel checks extend componentwise
by right quaternionic linearity.
"""
from __future__ import annotations

import argparse
import cmath
import math
import sys
from collections.abc import Callable
from typing import NamedTuple


class Axial(NamedTuple):
    p: float
    q: float


def kernels(z: complex, pole: complex) -> tuple[Axial, Axial]:
    """Return (U_pole, V_pole) as real axial component pairs."""
    x, r, u, v = z.real, z.imag, pole.real, pole.imag
    if r <= 0 or v <= 0 or z == pole:
        raise ValueError("Both points must lie above the real axis and differ.")
    d = abs(z - pole) ** 2
    ell = 0.5 * math.log(d)
    pv = (x - u) / (math.pi * r * d)
    qv = -(r - v) / (math.pi * r * d) + ell / (math.pi * r**2)
    pu = (x * (x - u) + r * (r - v)) / (math.pi * r * d)
    pu += ell / (math.pi * r)
    qu = (x * v - r * u) / (math.pi * r * d)
    qu += x * ell / (math.pi * r**2)
    return Axial(pu, qu), Axial(pv, qv)


def circle_integral(
    integrand: Callable[[complex, complex], complex],
    center: complex,
    radius: float,
    steps: int = 4096,
) -> complex:
    """Midpoint periodic trapezoidal quadrature, with z'(t) supplied."""
    if steps < 32 or radius <= 0 or center.imag <= radius:
        raise ValueError("Need at least 32 points and a circle strictly above R.")
    dt = math.tau / steps
    real, imag = [], []
    for k in range(steps):
        phase = cmath.exp(1j * (k + 0.5) * dt)
        z = center + radius * phase
        value = complex(integrand(z, 1j * radius * phase))
        real.append(value.real)
        imag.append(value.imag)
    return dt * complex(math.fsum(real), math.fsum(imag))


def check_close(name: str, actual: complex, expected: complex, tol: float) -> float:
    error = abs(actual - expected)
    if not math.isfinite(error) or error > tol:
        raise AssertionError(f"{name}: actual={actual!r}; expected={expected!r}; error={error}")
    print(f"PASS {name:40s} error={error:.3e}")
    return error


def numerical_checks() -> None:
    pole = complex(0.4, 1.3)
    radius = 0.35
    print("Numerical period checks (4096-point periodic quadrature)")
    for index, label, expected in [(0, "U", (1, 0)), (1, "V", (0, 1))]:
        def omega(z: complex, dz: complex) -> complex:
            p, q = kernels(z, pole)[index]
            return (-p * dz.real + q * dz.imag) / 2

        def theta(z: complex, dz: complex) -> complex:
            p, q = kernels(z, pole)[index]
            x, r = z.real, z.imag
            return ((x*p + r*q) * dz.real + (r*p - x*q) * dz.imag) / 2

        for name, fun, answer in [("omega", omega, expected[0]), ("theta", theta, expected[1])]:
            check_close(f"{label}: {name} period", circle_integral(fun, pole, radius), answer, 2e-11)

        def encoding(z: complex) -> complex:
            w = z - pole
            if index == 0:
                return 1/(2*math.pi*1j*w) - pole/(2*math.pi*1j*w*w)
            return -1/(2*math.pi*1j*w*w)

        check_close(f"{label}: integral J dz", circle_integral(lambda z, dz: encoding(z)*dz, pole, radius), expected[0], 2e-11)
        check_close(f"{label}: -integral z J dz", circle_integral(lambda z, dz: -z*encoding(z)*dz, pole, radius), expected[1], 2e-11)

    # On a loop not enclosing the pole, all modes must have zero periods.
    center = complex(-0.8, 1.5)
    for index, label in [(0, "U"), (1, "V")]:
        def omega_out(z: complex, dz: complex) -> complex:
            p, q = kernels(z, pole)[index]
            return (-p*dz.real+q*dz.imag)/2
        check_close(f"{label}: nonenclosing omega", circle_integral(omega_out, center, 0.15), 0, 2e-11)

    # Componentwise complex coefficients represent the four H_C coordinates.
    a = (0.2, -0.7, 1.1, 0.4)
    b = (-0.8, 0.6, 0.3, -0.2)
    c = (complex(0.5, 0.3), complex(-0.2, 0.8), complex(1, -0.1), complex(0.4, 0.7))
    k = 3
    for t in range(4):
        def jfull(z: complex) -> complex:
            w = z-pole
            return a[t]/(2*math.pi*1j*w) - (pole*a[t]+b[t])/(2*math.pi*1j*w*w) + k*(k+1)*c[t]/w**(k+2)
        recovered = circle_integral(lambda z, dz: (z-pole)**(k+1)*jfull(z)*dz, pole, radius)/(2*math.pi*1j*k*(k+1))
        check_close(f"multipole c_{k}, component {t}", recovered, c[t], 2e-11)
        j2 = -(pole*a[t]+b[t])/(2*math.pi*1j)
        j1 = a[t]/(2*math.pi*1j)
        check_close(f"residue constraint, component {t}", j1, 1j*j2.real/pole.imag, 2e-14)

    print("\nLeading critical norm: ratio rho*m_G / predicted_constant")
    a0, b0 = 0.7, -0.2
    target = abs(pole*a0+b0)/(math.pi*pole.imag)
    previous = float("inf")
    for rho in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        maxerr = 0.0
        for t in range(64):
            z = pole+rho*cmath.exp(1j*math.tau*(t+0.3)/64)
            uk, vk = kernels(z, pole)
            p, q = uk.p*a0+vk.p*b0, uk.q*a0+vk.q*b0
            ratio = rho*math.hypot(p,q)/target
            maxerr = max(maxerr, abs(ratio-1))
        print(f"rho={rho:.0e}: maximum angular ratio error={maxerr:.6e}")
        if maxerr >= previous:
            raise AssertionError("Critical asymptotic check did not improve as rho decreased.")
        previous = maxerr
    if previous > 1e-4:
        raise AssertionError("Critical asymptotic ratio failed to approach 1.")


def symbolic_checks() -> None:
    try:
        import sympy as s
    except ImportError as exc:
        raise RuntimeError("Install SymPy, or use --numerical-only.") from exc
    x, r, u, v = s.symbols("x r u v", real=True)
    d = (x-u)**2+(r-v)**2
    ell = s.log(d)/2
    pv = (x-u)/(s.pi*r*d)
    qv = -(r-v)/(s.pi*r*d)+ell/(s.pi*r**2)
    pu = (x*(x-u)+r*(r-v))/(s.pi*r*d)+ell/(s.pi*r)
    qu = (x*v-r*u)/(s.pi*r*d)+x*ell/(s.pi*r**2)
    z, pole = x+s.I*r, u+s.I*v

    def zero(name: str, expression: object) -> None:
        reduced = s.simplify(expression)
        if reduced != 0:
            raise AssertionError(f"{name}: nonzero residual {reduced}")
        print("PASS " + name)

    print(f"Symbolic checks (SymPy {s.__version__})")
    for label, p, q in [("U", pu, qu), ("V", pv, qv)]:
        zero(f"{label}: first Vekua equation", s.diff(p,x)-s.diff(q,r)-2*q/r)
        zero(f"{label}: second Vekua equation", s.diff(q,x)+s.diff(p,r))
        zero(f"{label}: omega closed", (s.diff(q,x)+s.diff(p,r))/2)
        zero(f"{label}: theta closed", (s.diff(r*p-x*q,x)-s.diff(x*p+r*q,r))/2)
        j = (-p+r*s.diff(q,x)-s.I*r*s.diff(p,x))/2
        expected = -1/(2*s.pi*s.I*(z-pole)**2) if label == "V" else 1/(2*s.pi*s.I*(z-pole))-pole/(2*s.pi*s.I*(z-pole)**2)
        zero(f"{label}: holomorphic encoding", s.together(j-expected))

    # Verify the first-order Fueter formula and T(Fu F)=F'' for basis stems.
    w = z-pole
    tests = [("z^2", z**2), ("iota*z", s.I*z), ("iota", s.I), ("pole", 1/w), ("iota*pole", s.I/w)]
    for name, f in tests:
        aa, bb = s.simplify(s.re(f)), s.simplify(s.im(f))
        p = 2*s.diff(aa,r)/r
        q = 2*s.diff(bb,r)/r-2*bb/r**2
        zero(f"{name}: first-order Fueter identity", q-s.I*p-2*s.diff(f,x)/r+2*bb/r**2)
        zero(f"{name}: T(Fu F)=F''", (-p+r*s.diff(q,x)-s.I*r*s.diff(p,x))/2-s.diff(f,x,2))

    e, h = s.symbols("e h", real=True)
    p, q = -2*e/r, -2*(x*e+h)/r**2
    zero("encoding kernel: Vekua 1", s.diff(p,x)-s.diff(q,r)-2*q/r)
    zero("encoding kernel: Vekua 2", s.diff(q,x)+s.diff(p,r))
    zero("encoding kernel: T=0", (-p+r*s.diff(q,x)-s.I*r*s.diff(p,x))/2)
    print()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical-only", action="store_true", help="Skip SymPy checks; use only the standard library.")
    args = parser.parse_args()
    try:
        if not args.numerical_only:
            symbolic_checks()
        numerical_checks()
    except (AssertionError, ValueError, RuntimeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    print("\nAll requested checks passed. These checks do not replace the proofs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
