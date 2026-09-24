#!/usr/bin/env python3
"""Reproducible checks for quaternionic_fueter_periods.tex.

Run: python verify.py
Requires Python 3.10+, NumPy and SymPy. This is a formula/experiment audit,
not a formal proof of the analytic or topological theorems. Quaternion
coefficients are represented in the fixed real basis (1, i, j, k). All
operations checked here are right-linear in those coefficients.
"""
from __future__ import annotations

import math
import sys
from typing import Callable

import numpy as np
import sympy as sp

Array = np.ndarray
Field = Callable[[Array, Array], tuple[Array, Array]]


def zero(expr: sp.Expr, name: str) -> None:
    """Require an exact symbolic identity, not a floating-point test."""
    simplified = sp.factor(sp.cancel(sp.together(sp.expand(expr))))
    if simplified != 0:
        simplified = sp.simplify(simplified)
    if simplified != 0:
        raise AssertionError(f"{name}: nonzero remainder {simplified}")
    print(f"PASS exact: {name}")


def symbolic_checks() -> None:
    x, r, u, v = sp.symbols("x r u v", real=True)
    a, b = sp.symbols("a b", real=True)
    t, s = x-u, r-v
    rho2 = t*t+s*s
    ell = sp.log(rho2)/2
    z, zeta = x+sp.I*r, u+sp.I*v
    p = ((x*a+b)*t/(r*rho2)+a*s/rho2+a*ell/r)/sp.pi
    q = (a*t/rho2-(x*a+b)*s/(r*rho2)+(x*a+b)*ell/r**2)/sp.pi
    # Keeping a,b symbolic verifies both independent scalar basis fields.
    zero(sp.diff(p, x)-sp.diff(q, r)-2*q/r,
         "Vekua equation 1 for both independent defects")
    zero(sp.diff(q, x)+sp.diff(p, r),
         "Vekua equation 2 for both independent defects")
    k = (-p+r*sp.diff(q, x)-sp.I*r*sp.diff(p, x))/2
    target = (a/(z-zeta)-(zeta*a+b)/(z-zeta)**2)/(2*sp.pi*sp.I)
    zero(k-target, "holomorphic invariant J(E) with arbitrary u,v,a,b")

    # A local branch theta has known derivatives. Work with theta as a
    # formal variable, applying the chain rule explicitly.
    theta = sp.Symbol("theta", real=True)
    def dx(expr: sp.Expr) -> sp.Expr:
        return sp.diff(expr, x)-s/rho2*sp.diff(expr, theta)
    def dr(expr: sp.Expr) -> sp.Expr:
        return sp.diff(expr, r)+t/rho2*sp.diff(expr, theta)
    A = ((x*a+b)*theta+r*a*ell)/(2*sp.pi)
    B = (r*a*theta-(x*a+b)*ell)/(2*sp.pi)
    C = B/r
    D = A-x*C
    zero(dx(A)-dr(B), "logarithmic stem CR equation 1")
    zero(dr(A)+dx(B), "logarithmic stem CR equation 2")
    zero(dx(C)+p/2, "direct first primitive: C_x = -P/2")
    zero(dr(C)-q/2, "direct first primitive: C_r = Q/2")
    zero(dx(D)-(x*p+r*q)/2, "direct second primitive: D_x")
    zero(dr(D)-(r*p-x*q)/2, "direct second primitive: D_r")
    zero(2*dr(A)/r-p, "direct Laplacian real component")
    zero(2*dr(B)/r-2*B/r**2-q, "direct Laplacian imaginary component")

    # Independent polynomial/rational sources test the differential
    # invariant and the formula used in the singularity proof.
    sources = [z**2, z**3, z**4, sp.I*z, sp.I,
               1/(z-(sp.Rational(1, 2)+2*sp.I))]
    for index, F in enumerate(sources, start=1):
        F = sp.expand_complex(F)
        A0, B0 = sp.re(F), sp.im(F)
        P = 2*sp.diff(A0, r)/r
        Q = 2*sp.diff(B0, r)/r-2*B0/r**2
        zero((-P+r*sp.diff(Q, x)-sp.I*r*sp.diff(P, x))/2-sp.diff(F,x,2),
             f"J(Delta F) = F'' for source {index}")
        zero(P+sp.I*Q-2*sp.I*sp.diff(F,x)/r+2*sp.I*B0/r**2,
             f"complexified Fueter image for source {index}")

    rho = sp.symbols("rho", positive=True)
    zero(sp.diff(sp.log(rho)+4*v/(v+rho),rho)
         -(v-rho)**2/(rho*(v+rho)**2),
         "finite-radius energy lower-bound integral")


def defect(x: Array, r: Array, u: float, v: float,
           a: Array, b: Array) -> tuple[Array, Array]:
    x = np.asarray(x, dtype=float)[..., None]
    r = np.asarray(r, dtype=float)[..., None]
    a, b = np.asarray(a, dtype=float), np.asarray(b, dtype=float)
    if a.shape != (4,) or b.shape != (4,):
        raise ValueError("Quaternion coefficient vectors must have shape (4,).")
    t, s = x-u, r-v
    rho2 = t*t+s*s
    if np.any(r == 0) or np.any(rho2 == 0):
        raise ValueError("Defect formula is evaluated on its excluded set.")
    ell = np.log(rho2)/2
    P = ((x*a+b)*t/(r*rho2)+a*s/rho2+a*ell/r)/np.pi
    Q = (a*t/rho2-(x*a+b)*s/(r*rho2)+(x*a+b)*ell/r**2)/np.pi
    return P, Q


def polar_defect(rho: Array, theta: Array, u: float, v: float,
                 a: Array, b: Array) -> tuple[Array, Array, Array]:
    """Stable broadcasted formulas, with quaternion coordinate last."""
    rho, theta = np.broadcast_arrays(rho, theta)
    rho, theta = rho[...,None], theta[...,None]
    si, co = np.sin(theta), np.cos(theta)
    r = v+rho*si
    d = u*a+b
    P = ((d*co+v*a*si)/rho+a*(1+np.log(rho)))/(np.pi*r)
    Q = ((v*a*co-d*si)/rho+(d+rho*a*co)*np.log(rho)/r)/(np.pi*r)
    return P,Q,r[...,0]


def periods(field: Field, center: complex, radius: float,
            n: int = 4096) -> tuple[Array, Array]:
    theta = (2*np.pi/n)*np.arange(n)
    x, r = center.real+radius*np.cos(theta), center.imag+radius*np.sin(theta)
    dx, dr = -radius*np.sin(theta), radius*np.cos(theta)
    P, Q = field(x,r)
    aa = np.sum((-P*dx[:,None]+Q*dr[:,None])/2,axis=0)*(2*np.pi/n)
    bb = np.sum(((x[:,None]*P+r[:,None]*Q)*dx[:,None]
                 +(r[:,None]*P-x[:,None]*Q)*dr[:,None])/2,
                axis=0)*(2*np.pi/n)
    return aa,bb


def near(actual: Array | float, target: Array | float,
         name: str, tolerance: float = 2e-10) -> None:
    err = float(np.max(np.abs(np.asarray(actual)-np.asarray(target))))
    if not math.isfinite(err) or err > tolerance:
        raise AssertionError(f"{name}: error {err:.6g} > tolerance {tolerance:.6g}")
    print(f"PASS numeric: {name}; max error={err:.3e}, tolerance={tolerance:.1e}")


def energy(epsilon: float, outer: float, u: float, v: float,
           a: Array, b: Array, radial_order: int = 96,
           angular_order: int = 1024) -> float:
    """4D energy via Gauss-Legendre in log(rho) and circle trapezoids."""
    if not 0 < epsilon < outer < v:
        raise ValueError("Require 0 < epsilon < outer < v.")
    nodes, weights = np.polynomial.legendre.leggauss(radial_order)
    lo,hi = np.log(epsilon),np.log(outer)
    tau = lo+(nodes+1)*(hi-lo)/2
    rho = np.exp(tau)[:,None]
    theta = 2*np.pi*np.arange(angular_order)[None,:]/angular_order
    P,Q,r = polar_defect(rho,theta,u,v,a,b)
    angular = (2*np.pi/angular_order)*np.sum(
        r*r*np.sum(P*P+Q*Q,axis=-1),axis=-1)
    # rho drho = rho^2 d(log rho).
    integrand = 4*np.pi*np.exp(2*tau)*angular
    return float((hi-lo)/2*np.dot(weights,integrand))


def numeric_checks() -> None:
    a = np.array([1.,2.,-1.,0.])
    b = np.array([0.,-1.,3.,1.])
    u,v = .5,2.
    zeta = complex(u,v)
    ea = np.array([1.,0.,0.,0.])
    ez = np.zeros(4)
    for av,bv,name in [(ea,ez,"first basis"),(ez,ea,"second basis"),
                       (a,b,"non-collinear quaternion coefficients")]:
        field = lambda x,r,av=av,bv=bv: defect(x,r,u,v,av,bv)
        for radius in [.1,.4,.9]:
            aa,bb = periods(field,zeta,radius)
            near(aa,av,f"{name}, a-period, radius {radius}")
            near(bb,bv,f"{name}, b-period, radius {radius}")
        aa,bb = periods(field,zeta+1.5,.3)
        near(aa,ez,f"{name}, zero winding a-period")
        near(bb,ez,f"{name}, zero winding b-period")

    theta = np.linspace(0,2*np.pi,1000,endpoint=False)
    radius = .37
    P,Q = defect(u+radius*np.cos(theta),v+radius*np.sin(theta),u,v,a,b)
    Pp,Qp,_ = polar_defect(np.asarray(radius),theta,u,v,a,b)
    near(P,Pp,"branch-free Cartesian/polar real-component agreement")
    near(Q,Qp,"branch-free Cartesian/polar imaginary-component agreement")

    # Two-hole correction, with a nonzero globally integrable polynomial
    # field added. Delta(q^2 c) = -4c.
    z2 = complex(2.,2.5)
    a2,b2 = np.array([0.,1.,0.,1.]),np.array([2.,0.,-1.,1.])
    c = np.array([1.,-1.,.25,.5])
    def combined(x: Array,r: Array) -> tuple[Array,Array]:
        p1,q1 = defect(x,r,u,v,a,b)
        p2,q2 = defect(x,r,z2.real,z2.imag,a2,b2)
        return p1+p2-4*c,q1+q2
    recovered = []
    for center,av,bv in [(zeta,a,b),(z2,a2,b2)]:
        aa,bb = periods(combined,center,.2)
        near(aa,av,f"two-hole assignment at {center}, a")
        near(bb,bv,f"two-hole assignment at {center}, b")
        recovered.append((center,aa,bb))
    def corrected(x: Array,r: Array) -> tuple[Array,Array]:
        P,Q = combined(x,r)
        for center,av,bv in recovered:
            p,q = defect(x,r,center.real,center.imag,av,bv)
            P,Q = P-p,Q-q
        return P,Q
    for center,_,_ in recovered:
        aa,bb = periods(corrected,center,.2)
        near(aa,ez,f"finite-rank correction at {center}, a")
        near(bb,ez,f"finite-rank correction at {center}, b")

    # Coefficient predicted by the proof, independently from quadrature.
    W = float(np.dot(u*a+b,u*a+b)+v*v*np.dot(a,a))
    target = 8*W
    near(W,31.5,"quadratic residue invariant W",1e-13)
    near(target,252.,"predicted logarithmic energy coefficient",1e-12)
    print("\nENERGY ON SHRINKING DECADE ANNULI")
    print("epsilon           E(epsilon,10epsilon)/log(10)     error from 252")
    ratios = []
    for epsilon in [1e-2,1e-3,1e-4,1e-5,1e-6]:
        ratio = energy(epsilon,10*epsilon,u,v,a,b)/np.log(10)
        ratios.append(ratio)
        print(f"{epsilon:8.1e}          {ratio:24.12f}       {ratio-target:+.6e}")
    near(ratios[-1],target,"small-annulus energy coefficient",2e-6)
    # Repeat final value at a different quadrature resolution.
    alternate = energy(1e-6,1e-5,u,v,a,b,radial_order=64,angular_order=512)/np.log(10)
    near(alternate,ratios[-1],"energy quadrature resolution check",2e-9)

    R = .3
    print("\nFINITE RENORMALIZED ENERGY AT OUTER RADIUS 0.3")
    print("epsilon             E(epsilon,R)-252 log(R/epsilon)")
    renormalized = []
    for epsilon in [1e-2,1e-3,1e-4,1e-5,1e-6]:
        value = energy(epsilon,R,u,v,a,b)
        remainder = value-target*np.log(R/epsilon)
        renormalized.append(remainder)
        print(f"{epsilon:8.1e}                  {remainder:24.12f}")
        lower = target*(np.log(R/epsilon)+4*v/(v+R)-4*v/(v+epsilon))
        if value < lower-1e-8:
            raise AssertionError("Universal energy lower bound failed numerically.")
    near(renormalized[-1],renormalized[-2],
         "renormalized-energy stabilization",5e-5)
    print("PASS numeric: universal lower bound at all five truncation radii")


def main() -> None:
    print("Formula and numerical audit: global Fueter primitives and spherical singularities")
    print(f"Python {sys.version.split()[0]}, SymPy {sp.__version__}, NumPy {np.__version__}")
    print("All integrals use counterclockwise orientation and Euclidean volume.\n")
    symbolic_checks()
    print()
    numeric_checks()
    print("\nALL CHECKS PASSED.")
    print("These checks support the formulas; the article supplies the actual proofs.")


if __name__ == "__main__":
    main()
