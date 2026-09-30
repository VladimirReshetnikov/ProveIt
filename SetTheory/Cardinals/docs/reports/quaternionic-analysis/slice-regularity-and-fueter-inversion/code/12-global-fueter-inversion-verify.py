#!/usr/bin/env python3
"""Finite diagnostics for Global Fueter Inversion Beyond Finite Connectivity.

These tests are not a formal verification of the all-order or global theorems.
Run from the package directory: python code/verify.py
Requires Python 3.10+, SymPy and mpmath. No network access is used.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from collections import defaultdict
from pathlib import Path
from time import perf_counter

import mpmath as mp
import sympy as sp

x, y, t = sp.symbols("x y t", real=True)
P, Q, Px, Py, Qx, Qy = sp.symbols("P Q Px Py Qx Qy", real=True)


def zero(expr: sp.Expr, label: str) -> None:
    if sp.cancel(sp.expand(expr)) != 0:
        raise AssertionError(f"Identity failed: {label}: {sp.simplify(expr)}")


def constants(h: int) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    c = sp.Integer(2)**h * sp.factorial(h)
    C = (-1)**h * c**2
    k = sp.Rational((-1)**(h+1), 2**(2*h-1)*math.factorial(h)*math.factorial(h-1))
    return c, C, k


def radial(A: sp.Expr, B: sp.Expr, h: int) -> tuple[sp.Expr, sp.Expr]:
    for _ in range(h):
        A = sp.cancel(sp.diff(A, y)/y)
        B = sp.cancel(sp.diff(B/y, y))
    c, _, _ = constants(h)
    return sp.expand(c*A), sp.expand(c*B)


def current(h: int, p: sp.Expr = P, q: sp.Expr = Q) -> tuple[sp.Expr, sp.Expr]:
    _, _, k = constants(h)
    R = (t-x)**2+y**2
    return (k*R**(h-1)*((x-t)*p+y*q),
            k*R**(h-1)*(y*p-(x-t)*q))


def exact_checks(max_h: int) -> dict:
    counts = {"closedness": 0, "reflection": 0, "injectivity_evaluations": 0,
              "normalization": 0, "imaginary_constant": 0,
              "monomial_Hermite_identities": 0, "axis_confluence": 0,
              "calibration_monomials": 0, "reflection_homology_matrices": 0,
              "tangent_norm_identity": 0}
    for h in range(1, max(8, max_h)+1):
        c, C, k = constants(h)
        zero(k*C+2*h, f"normalization h={h}")
        counts["normalization"] += 1
        A, B = current(h)
        dBdx = sp.diff(B,x)+sp.diff(B,P)*Px+sp.diff(B,Q)*Qx
        dAdy = sp.diff(A,y)+sp.diff(A,P)*Py+sp.diff(A,Q)*Qy
        zero((dBdx-dAdy).subs({Px: Qy+2*h*Q/y, Py: -Qx}), f"closed h={h}")
        counts["closedness"] += 1
        zero(A.subs({y:-y,Q:-Q}, simultaneous=True)-A, f"reflection dx h={h}")
        zero(-B.subs({y:-y,Q:-Q}, simultaneous=True)-B, f"reflection dy h={h}")
        counts["reflection"] += 2
        zero(A.subs(t,x)-k*y**(2*h-1)*Q, f"injectivity Q h={h}")
        zero(B.subs(t,x)-k*y**(2*h-1)*P, f"injectivity P h={h}")
        counts["injectivity_evaluations"] += 2
        p, q = radial(sp.Integer(0), sp.Integer(1), h)
        zero(p, f"imaginary constant P h={h}")
        zero(q-(-1)**h*sp.factorial(2*h)/y**(2*h), f"imaginary constant Q h={h}")
        counts["imaginary_constant"] += 1

    for h in range(1, max_h+1):
        _, C, _ = constants(h)
        divisor = sp.Poly(((t-x)**2+y**2)**h, t)
        for degree in range(2*h+5):
            F = sp.expand((x+sp.I*y)**degree)
            real, imag = sp.expand_complex(F).as_real_imag()
            p, q = radial(real, imag, h)
            H = sp.rem(sp.Poly(t**degree,t), divisor).as_expr()
            A, B = current(h, p, q)
            zero(sp.diff(H,x)-A, f"Hermite dx h={h} k={degree}")
            zero(sp.diff(H,y)-B, f"Hermite dy h={h} k={degree}")
            counts["monomial_Hermite_identities"] += 1
            Taylor = sum(sp.binomial(degree,j)*x**(degree-j)*(t-x)**j
                         for j in range(min(degree,2*h-1)+1))
            zero(H.subs(y,0)-Taylor, f"confluence h={h} k={degree}")
            counts["axis_confluence"] += 1
            if degree <= 2*h+1:
                expected_p = 0 if degree < 2*h else C if degree == 2*h else C*(2*h+1)*x
                expected_q = C*y if degree == 2*h+1 else 0
                zero(p-expected_p, f"calibration P h={h} k={degree}")
                zero(q-expected_q, f"calibration Q h={h} k={degree}")
                counts["calibration_monomials"] += 1

    for paired in range(7):
        for fixed in range(7):
            n = 2*paired+fixed
            J = sp.zeros(n)
            for j in range(paired):
                J[2*j,2*j+1] = J[2*j+1,2*j] = -1
            for j in range(2*paired,n):
                J[j,j] = -1
            assert J*J == sp.eye(n)
            assert n-(J-sp.eye(n)).rank() == paired
            counts["reflection_homology_matrices"] += 1

    a, b, u, v = sp.symbols("a b u v", real=True)
    zero((a*u+b*v)**2+(b*u-a*v)**2-(a*a+b*b)*(u*u+v*v), "tangent identity")
    counts["tangent_norm_identity"] += 1
    return counts


def radial_coefficients(h: int, kind: str) -> dict[tuple[int,int], int]:
    terms = {(0,0): 1}
    for _ in range(h):
        new = defaultdict(int)
        for (power, derivative), coefficient in terms.items():
            new[(power-2,derivative)] += coefficient*(power-(kind == "S"))
            new[(power-1,derivative+1)] += coefficient
        terms = {key:value for key,value in new.items() if value}
    return terms


def paired_log_target(z: mp.mpc, h: int) -> tuple[mp.mpf,mp.mpf]:
    """Image of (1+z)/(2*pi*i) * (log(z-i)-log(z+i)); either local branch."""
    def logjet(k: int) -> mp.mpc:
        if k == 0:
            return mp.log(z-mp.j)-mp.log(z+mp.j)
        return (-1)**(k-1)*math.factorial(k-1)*((z-mp.j)**(-k)-(z+mp.j)**(-k))
    jets = []
    for k in range(h+1):
        value = (1+z)*logjet(k)
        if k:
            value += k*logjet(k-1)
        jets.append(value/(2*mp.pi*mp.j))
    c = 2**h*math.factorial(h)
    yy = z.imag
    p = c*sum(co*yy**power*(mp.j**k*jets[k]).real
              for (power,k),co in radial_coefficients(h,"R").items())
    q = c*sum(co*yy**power*(mp.j**k*jets[k]).imag
              for (power,k),co in radial_coefficients(h,"S").items())
    return p,q


def numerical_checks(nodes: int = 192) -> list[dict]:
    mp.mp.dps = 60
    results = []
    dx,dy = sp.symbols("dx dy", real=True)
    for h in range(1,4):
        A,B = current(h)
        coeffs = sp.Poly(sp.expand(A*dx+B*dy),t)
        fn = sp.lambdify((x,y,P,Q,dx,dy),
                         [coeffs.nth(j) for j in range(2*h)],"mpmath")
        for name, center, radius, sign in [
            ("upper",mp.j,mp.mpf(1)/5,1),
            ("lower",-mp.j,mp.mpf(1)/5,-1),
            ("real_center",mp.mpc(0),mp.mpf(1)/4,0)]:
            sums = [mp.mpf(0) for _ in range(2*h)]
            for k in range(nodes):
                angle = 2*mp.pi*(mp.mpf(k)+mp.mpf("0.371"))/nodes
                unit = mp.exp(mp.j*angle)
                z = center+radius*unit
                tangent = mp.j*radius*unit
                p,q = paired_log_target(z,h)
                values = fn(z.real,z.imag,p,q,tangent.real,tangent.imag)
                for j,value in enumerate(values):
                    sums[j] += value
            periods = [value*2*mp.pi/nodes for value in sums]
            error = max(abs(value-(sign if j<2 else 0)) for j,value in enumerate(periods))
            if error >= mp.mpf("1e-25"):
                raise AssertionError(f"Numerical diagnostic failed: h={h}, {name}, error={error}")
            results.append({"h":h,"loop":name,"nodes":nodes,
                            "observed_max_abs_error":mp.nstr(error,12),
                            "period_coefficients":[mp.nstr(value,20) for value in periods]})
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-h",type=int,default=5)
    parser.add_argument("--skip-numerical",action="store_true")
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"data"/"verification.json")
    args = parser.parse_args()
    if not 1 <= args.max_h <= 8:
        parser.error("--max-h must lie between 1 and 8")
    start = perf_counter()
    results = {"status":"PASS", "scope":"finite diagnostics, not formal theorem verification",
               "versions":{"python":platform.python_version(),"sympy":sp.__version__,"mpmath":mp.__version__},
               "exact":exact_checks(args.max_h),
               "numerical":[] if args.skip_numerical else numerical_checks(),
               "max_h_monomials":args.max_h}
    results["runtime_seconds"] = round(perf_counter()-start,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
