#!/usr/bin/env python3
"""Finite exact checks for Three-Dimensional Surreal Vector and Tensor Fields.

Requires Python 3.10+ and SymPy. Run: python verify_examples.py
These computations verify the displayed finite examples and identities, not
infinite Hahn summability, PDE existence, Hodge theory, or novelty claims.
All parameters are symbolic; no floating-point sampling is used.
"""
from __future__ import annotations

import sys
from collections.abc import Callable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

x, y, z, t, s = sp.symbols("x y z t s", real=True)
coords = (x, y, z)
Vector = sp.Matrix


def grad(f: sp.Expr) -> sp.Matrix:
    return Vector([sp.diff(f, q) for q in coords])


def div(v: sp.Matrix) -> sp.Expr:
    return sum(sp.diff(v[i], coords[i]) for i in range(3))


def curl(v: sp.Matrix) -> sp.Matrix:
    return Vector([
        sp.diff(v[2], y) - sp.diff(v[1], z),
        sp.diff(v[0], z) - sp.diff(v[2], x),
        sp.diff(v[1], x) - sp.diff(v[0], y),
    ])


def lap(f: sp.Expr) -> sp.Expr:
    return sum(sp.diff(f, q, 2) for q in coords)


def exact_zero(value: sp.Expr | sp.Matrix, label: str = "identity") -> None:
    entries = list(value) if isinstance(value, sp.MatrixBase) else [value]
    for entry in entries:
        result = sp.simplify(sp.expand(entry))
        if result != 0:
            raise AssertionError(f"{label}: nonzero remainder {result}")


def algebra() -> None:
    u = Vector(sp.symbols("u0:3"))
    v = Vector(sp.symbols("v0:3"))
    w = Vector(sp.symbols("w0:3"))
    exact_zero(u.cross(v).dot(u.cross(v)) - (u.dot(u)*v.dot(v)-u.dot(v)**2), "Lagrange")
    exact_zero(u.cross(v.cross(w)) - (v*u.dot(w)-w*u.dot(v)), "triple product")
    a, b, c = sp.symbols("a b c", nonzero=True)
    L = sp.diag(a, b, c)
    exact_zero((L*u).cross(L*v)-L.det()*L.inv().T*u.cross(v), "affine cross product")


def differential_identities() -> None:
    f = x**3*y + y**2*z + x*z**2
    v = Vector([x*y*z + t*x**2, y**3+t**-1*z, z**2*x+t**2*y])
    w = Vector([y*z, x**2, z+y])
    exact_zero(curl(grad(f)), "curl grad")
    exact_zero(div(curl(v)), "div curl")
    exact_zero(curl(curl(v))-grad(div(v))+v.applyfunc(lap), "curl curl")
    exact_zero(div(v.cross(w)) - w.dot(curl(v)) + v.dot(curl(w)), "cross product divergence")


def box_flux() -> None:
    a, b, c = sp.symbols("a b c", positive=True)
    v = Vector([x**2,y**2,z**2])
    volume = sp.integrate(div(v), (x,0,a), (y,0,b), (z,0,c))
    flux = (sp.integrate(v[0].subs(x,a)-v[0].subs(x,0),(y,0,b),(z,0,c))
            + sp.integrate(v[1].subs(y,b)-v[1].subs(y,0),(x,0,a),(z,0,c))
            + sp.integrate(v[2].subs(z,c)-v[2].subs(z,0),(x,0,a),(y,0,b)))
    exact_zero(volume-flux, "box divergence theorem")
    exact_zero(volume-a*b*c*(a+b+c), "box formula")


def radial_potentials() -> None:
    r = Vector(coords)
    phi = x*x*y+y*y*z+z*z*x
    v = grad(phi)
    rescaled = v.subs({x:s*x,y:s*y,z:s*z}, simultaneous=True)
    potential = sp.integrate(r.dot(rescaled),(s,0,1))
    exact_zero(potential-phi, "radial scalar potential")
    B = Vector([x,y,-2*z])
    Bscaled = B.subs({x:s*x,y:s*y,z:s*z}, simultaneous=True)
    integral = Bscaled.applyfunc(lambda entry: sp.integrate(s*entry,(s,0,1)))
    A = -r.cross(integral)
    exact_zero(curl(A)-B, "radial vector potential")


def conformal_curvature() -> None:
    """Derive Ricci from Christoffel symbols, not from the scalar formula."""
    delta = lambda i,j: sp.Integer(i==j)
    Gamma = [[[t*(delta(k,i)*coords[j]+delta(k,j)*coords[i]-delta(i,j)*coords[k])
               for j in range(3)] for i in range(3)] for k in range(3)]
    # R^k_{ell i j} = d_i Gamma^k_{j ell} - d_j Gamma^k_{i ell}
    #                  + Gamma^k_{i a} Gamma^a_{j ell}
    #                  - Gamma^k_{j a} Gamma^a_{i ell}.
    def R(k: int, ell: int, i: int, j: int) -> sp.Expr:
        return (sp.diff(Gamma[k][j][ell], coords[i])
                -sp.diff(Gamma[k][i][ell], coords[j])
                +sum(Gamma[k][i][a]*Gamma[a][j][ell]
                     -Gamma[k][j][a]*Gamma[a][i][ell] for a in range(3)))
    Ric = sp.Matrix(3,3, lambda ell,j: sp.expand(sum(R(k,ell,k,j) for k in range(3))))
    radius2 = x*x+y*y+z*z
    expected_Ric = t*t*Vector(coords)*Vector(coords).T-(4*t+t*t*radius2)*sp.eye(3)
    exact_zero(Ric-expected_Ric, "conformal Ricci")
    scalar = sp.exp(-t*radius2)*sp.trace(Ric)
    exact_zero(scalar-sp.exp(-t*radius2)*(-12*t-2*t*t*radius2), "conformal scalar curvature")


def scale_connection() -> None:
    a = Vector([0,x,0])
    b = curl(a)
    def D(f: sp.Expr) -> sp.Expr:
        return t*sp.diff(f,t)
    def nabla(f: sp.Expr,i: int) -> sp.Expr:
        return sp.diff(f,coords[i])+a[i]*D(f)
    def cov_grad(f: sp.Expr) -> sp.Matrix:
        return Vector([nabla(f,i) for i in range(3)])
    def cov_curl(v: sp.Matrix) -> sp.Matrix:
        return Vector([nabla(v[2],1)-nabla(v[1],2),
                       nabla(v[0],2)-nabla(v[2],0),
                       nabla(v[1],0)-nabla(v[0],1)])
    def cov_div(v: sp.Matrix) -> sp.Expr:
        return sum(nabla(v[i],i) for i in range(3))
    f = t**-1*x*y+t**2*y*z+t**3*x*z
    v = Vector([t*x*y, t**-1*z*x, t**2*(x+y+z)])
    exact_zero(cov_curl(cov_grad(f))-b*D(f), "scale curl grad")
    exact_zero(cov_div(cov_curl(v))-b.dot(v.applyfunc(D)), "scale div curl")


def elasticity() -> None:
    aa,bb,cc,dd,ee,ff,lam,mu = sp.symbols("aa bb cc dd ee ff lam mu", real=True)
    strain = Vector([[aa,dd,ee],[dd,bb,ff],[ee,ff,cc]])
    trace = sp.trace(strain)
    dev = strain-sp.eye(3)*trace/3
    frob = lambda A: sum(entry**2 for entry in A)
    energy = lam*trace**2/2+mu*frob(strain)
    exact_zero(energy-mu*frob(dev)-(3*lam+2*mu)*trace**2/6, "elastic energy split")


def beltrami() -> None:
    amplitude = t**-1+t**2
    u = amplitude*Vector([sp.sin(z),sp.cos(z),0])
    exact_zero(div(u), "Beltrami divergence")
    exact_zero(curl(u)-u, "Beltrami curl")
    exact_zero(u.applyfunc(lap)+u, "Beltrami Laplacian")
    exact_zero(u.jacobian(coords)*u, "Beltrami convection")
    exact_zero(u.dot(u)-(t**-2+2*t+t**4), "multiscale energy")


def catalan_recursion() -> None:
    nmax = 12
    coeff = {1:sp.Integer(1)}
    for n in range(2,nmax+1):
        coeff[n] = -sum(coeff[i]*coeff[n-i] for i in range(1,n))
    u = sum(coeff[n]*t**n for n in range(1,nmax+1))
    residual = sp.Poly(sp.expand(u+u*u-t),t)
    for n in range(nmax+1):
        exact_zero(residual.nth(n), f"quadratic residual, degree {n}")
    for n in range(1,nmax+1):
        exact_zero(coeff[n]-(-1)**(n-1)*sp.catalan(n-1), "Catalan coefficient")
    root_series = ((sp.sqrt(1+4*t)-1)/2).series(t,0,nmax+1).removeO()
    exact_zero(u-root_series,"quadratic root branch")


def softened_source() -> None:
    q,a = sp.symbols("q a", positive=True)
    R = x*x+y*y+z*z+a*a
    B = q*Vector(coords)/R**sp.Rational(3,2)
    exact_zero(div(B)-3*q*a*a/R**sp.Rational(5,2), "softened monopole source")


def worked_field() -> None:
    V = Vector([2*t**-1*x*y+t*x*z+t*t,
                t**-1*x*x-t*y*z+2*t*t, 3*t*t])
    exact_zero(div(V)-2*t**-1*y, "worked divergence")
    exact_zero(curl(V)-t*Vector([y,x,0]), "worked curl")
    leading = grad(x*x*y)
    next_term = curl(Vector([0,0,x*y*z]))
    exact_zero(leading.dot(next_term)-x*x*y*z, "worked mixed scale")


TESTS: list[tuple[str,Callable[[],None]]] = [
    ("Finite vector identities and anisotropic cross-product rule",algebra),
    ("Spatial grad/div/curl identities",differential_identities),
    ("Polynomial-box divergence theorem",box_flux),
    ("Support-preserving radial potential formulas",radial_potentials),
    ("Conformal Ricci and scalar curvature from Christoffel symbols",conformal_curvature),
    ("Scale-connection curl/gradient and divergence/curl defects",scale_connection),
    ("Isotropic elastic energy decomposition",elasticity),
    ("Exact multiscale Beltrami field",beltrami),
    ("Quadratic lifting / Catalan recursion through degree 12",catalan_recursion),
    ("Softened monopole source density",softened_source),
    ("Worked three-scale field",worked_field),
]


def main() -> int:
    print("Finite symbolic checks for Surreal Vector and Tensor Fields")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("All arithmetic is exact. These checks are not proofs of infinite support theorems.\n")
    for name, test in TESTS:
        try:
            test()
        except Exception as exc:
            print(f"FAIL  {name}: {exc}")
            return 1
        print(f"PASS  {name}")
    print(f"\nResult: {len(TESTS)} / {len(TESTS)} check groups passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
