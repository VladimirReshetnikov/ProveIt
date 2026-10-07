#!/usr/bin/env python3
"""Reproducible checks for sharp_missing_intervals.tex.

The mathematical proofs are in the manuscript. Floating-point linear programs,
root finding, and symbolic simplifications below are regression checks, not a
formal verification of the theorems. No network access is used.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import numpy as np
import scipy
import sympy as sp
from scipy.optimize import linprog


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def certificate(R: int, a: float) -> dict:
    if R < 1 or not math.pi / (R + 1) < a < 2 * math.pi / (R + 1):
        raise ValueError("Parameters must lie in the strict first window.")
    m = R + 1
    c = math.cos(a)
    S = m - math.tan(m * a / 2) / math.tan(a / 2)
    d = 1 / S
    rho = 1 / (S - 1)
    j = np.arange(R)
    w = (1 - np.cos((j - (R - 1) / 2) * a) / math.cos(m * a / 2)) / S
    A = np.r_[np.correlate(w, w, "full")[R - 1:], 0.0, 0.0]
    q = np.array([A[1] - c * A[0]] +
                 [(A[k - 1] + A[k + 1]) / 2 - c * A[k]
                  for k in range(1, R + 1)])
    T = np.diag(np.full(R - 1, .5), 1) + np.diag(np.full(R - 1, .5), -1)
    return dict(R=R, a=a, c=c, S=S, d=d, rho=rho, w=w, q=q,
                f=q / (1 - c), T=T)


def check_symbolic() -> dict:
    count = 0
    for R in range(1, 9):
        w = sp.symbols(f"w0:{R}")
        c, lam = sp.symbols("c lam")
        at = lambda j: w[j] if 0 <= j < R else sp.S.Zero
        ac = lambda k: sum((at(j) * at(j + k) for j in range(R)), sp.S.Zero)
        for k in range(1, R + 1):
            q = (ac(k - 1) + ac(k + 1)) / 2 - c * ac(k)
            target = lam * sum(w[:R-k]) + w[R-k] * w[R-1] / 2
            residual = sum(w[j] * ((at(j+k-1) + at(j+k+1)) / 2
                                    - c * at(j+k) - lam)
                           for j in range(R-k))
            require(sp.expand(q - target - residual) == 0, "Coefficient identity")
            count += 1
    c = sp.symbols("c")
    rho = (1 - 2*c) / (3 - 2*c)
    u = 1 / ((3 - 2*c)*(1+c))
    v = 1 - 2*u
    require(sp.factor(2*u*c - v + rho) == 0, "R=2 first moment")
    require(sp.factor(2*u*(2*c*c-1) + v + rho) == 0, "R=2 second moment")
    return {"autocorrelation_polynomial_identities": count,
            "R2_exact_moment_identities": 2}


def check_certificates() -> dict:
    errors = dict(sum_w=0.0, recurrence=0.0, coefficient_identity=0.0,
                  root_modulus=0.0, extremal_moments=0.0,
                  localizing_negative_eigenvalue=0.0)
    rows = []
    for R in range(1, 25):
        for t in (1.03, 1.2, 1.5, 1.8, 1.97):
            p = certificate(R, t * math.pi / (R+1))
            a,c,d,rho,w,q,T = (p[k] for k in ("a","c","d","rho","w","q","T"))
            lam = (1-c)*d
            errors["sum_w"] = max(errors["sum_w"], abs(sum(w)-1))
            errors["recurrence"] = max(errors["recurrence"],
                float(np.max(np.abs((T-c*np.eye(R)) @ w - lam))))
            require(np.min(w)>0 and np.min(q)>0, "Strict coefficient positivity")
            q2 = [lam] + [lam*sum(w[:R-k]) + w[R-k]*w[-1]/2
                           for k in range(1,R+1)]
            errors["coefficient_identity"] = max(errors["coefficient_identity"],
                float(np.max(np.abs(q-q2))))
            L = (1+rho)*(c*np.eye(R)-T) + rho*(1-c)*np.ones((R,R))
            errors["localizing_negative_eigenvalue"] = max(
                errors["localizing_negative_eigenvalue"],
                max(0.0, -float(np.linalg.eigvalsh(L)[0])))
            roots = np.roots(w[::-1]) if R>1 else np.array([], dtype=complex)
            if R>1:
                errors["root_modulus"] = max(errors["root_modulus"],
                                              float(np.max(abs(abs(roots)-1))))
                require(np.all(abs(np.angle(roots)) > a+1e-9), "Root arc location")
            theta = np.sort(np.r_[-a, np.angle(roots), a])
            freq = np.arange(-R, R+1)
            V = np.exp(-1j*np.outer(freq,theta))
            target = np.full(2*R+1,-rho)
            target[R] = 1
            weights = np.linalg.lstsq(V,target,rcond=None)[0]
            errors["extremal_moments"] = max(errors["extremal_moments"],
                float(np.max(abs(V@weights-target))), float(np.max(abs(weights.imag))))
            require(np.min(weights.real)>0, "Extremal weights strictly positive")
            rows.append({"R":R,"window_coordinate":t,"rho":rho,
                         "minimum_weight":float(min(weights.real))})
    for name,value in errors.items():
        require(value < 1e-8, f"Numerical residual too large: {name}={value}")
    return {"cases":len(rows),"maximum_absolute_residuals":errors,"examples":rows}


def check_linear_programs() -> dict:
    errors = []
    robust_errors = []
    for R in range(1,11):
        for t in (1.05,1.2,1.5,1.8,1.98):
            a = t*math.pi/(R+1)
            p = certificate(R,a)
            theta = np.linspace(a,math.pi,2001)
            C = np.cos(np.outer(np.arange(1,R+1),theta))
            res = linprog(np.r_[np.zeros(len(theta)),1],
                A_ub=np.c_[np.r_[C,-C],-np.ones(2*R)], b_ub=np.zeros(2*R),
                A_eq=[np.r_[np.ones(len(theta)),0]],b_eq=[1],
                bounds=[(0,None)]*(len(theta)+1), method="highs")
            require(res.success, "Gap LP failed")
            errors.append(float(res.fun-p["rho"]))
            # A separate mass minimization: include the analytically specified
            # contact points so mesh error cannot hide an equality failure.
            roots = np.roots(p["w"][::-1]) if R>1 else []
            grid = np.unique(np.r_[np.linspace(0,math.pi,1001),0,a,
                                   abs(np.angle(roots))])
            C = np.cos(np.outer(np.arange(1,R+1),grid))
            objective = (grid < a-1e-10).astype(float)
            for s in (0.0,.25,.75,1.0):
                eps = s*p["rho"]
                res = linprog(objective,A_ub=np.r_[C,-C],b_ub=np.full(2*R,eps),
                    A_eq=[np.ones(len(grid))],b_eq=[1],bounds=(0,None),method="highs")
                require(res.success,"Mass LP failed")
                exact = (p["rho"]-eps)/(1+p["rho"])
                robust_errors.append(abs(float(res.fun)-exact))
    require(min(errors)>-3e-8 and max(errors)<2e-5, "Gap LP discrepancy")
    require(max(robust_errors)<3e-7, "Mass LP discrepancy")
    return {"gap_LPs":len(errors),"gap_mesh_points":2001,
            "gap_LP_minus_formula_min":min(errors),
            "gap_LP_minus_formula_max":max(errors),
            "mass_LPs":len(robust_errors),
            "mass_max_absolute_error":max(robust_errors),
            "note":"Floating-point LPs are not mathematical certificates."}


def check_finite_cyclic() -> dict:
    cases = 0
    minimum_slack = math.inf
    for N in range(3,13):
        for M in range(1,N//2+1):
            available = [j for j in range(N) if min(j,N-j)>=M]
            R = N//M-1
            for mask in range(1,1<<len(available)):
                w = np.zeros(N)
                for k,j in enumerate(available):
                    w[j] = bool(mask & (1<<k))
                values = -np.fft.fft(w)[1:R+1].real
                slack = float(max(values) - M/(N-M)*sum(w))
                minimum_slack = min(minimum_slack,slack)
                require(slack>=-1e-9,"Finite cyclic one-sided bound")
                cases += 1
    return {"nonempty_indicator_cases":cases,"N_min":3,"N_max":12,
            "minimum_slack":minimum_slack,
            "note":"Floating-point Fourier checks; all integer subsets enumerated in range."}


def check_critical_stability(rng: np.random.Generator) -> dict:
    cases = 0
    minimum_slack = math.inf
    for R in range(1,31):
        m = R+1
        beta = math.pi/m
        nodes = (2*np.arange(m)+1)*math.pi/m
        for _ in range(10):
            theta = rng.uniform(beta,2*math.pi-beta,100)
            weights = rng.dirichlet(np.ones(len(theta)))
            eps = float(max(abs(np.exp(-1j*np.outer(np.arange(1,R+1),theta))@weights)))
            dist = np.min(abs(np.angle(np.exp(1j*(theta[:,None]-nodes)))),axis=1)
            lhs = float(weights@(dist*dist))
            rhs = (math.pi/m/math.tan(beta/2))**2*eps
            minimum_slack = min(minimum_slack,rhs-lhs)
            require(lhs<=rhs+1e-10,"Critical geometric stability")
            cases += 1
    return {"random_measures":cases,"minimum_slack":minimum_slack}


def check_rounding(rng: np.random.Generator) -> dict:
    for _ in range(1000):
        k = int(rng.integers(2,9)); D = int(rng.integers(1,7))
        B = int(rng.integers(1,7)); n = int(rng.integers(2,16))
        delta = Fraction(1,n); s = (delta/B)**D
        T = math.ceil(16/(delta*s))+int(rng.integers(0,100))
        Q = math.floor(Fraction(T**k)*s/4)
        r = n-1; q = math.floor(2/s); p = r*q
        require(Q>=Fraction(T**k)*s/8,"Dirichlet rounding")
        require(1<=p<=Fraction(T,8),"Recurrence length")
        require(Fraction(p**(k-1),Q)<=delta/2,"Recurrence error")
    return {"exact_rational_rounding_cases":1000,
            "note":"Checks the arithmetic inequalities, not the external Weyl estimate."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path("verification_results.json"))
    args = parser.parse_args()
    rng = np.random.default_rng(20261006)
    report = {"status":"PASS", "seed":20261006,
              "versions":{"python":platform.python_version(),"numpy":np.__version__,
                          "scipy":scipy.__version__,"sympy":sp.__version__},
              "symbolic":check_symbolic(),"certificates":check_certificates(),
              "linear_programs":check_linear_programs(),"finite_cyclic":check_finite_cyclic(),
              "critical_stability":check_critical_stability(rng),
              "rounding":check_rounding(rng),
              "limitations":"Not a proof-assistant verification or a priority audit."}
    args.output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in report.items() if k!="certificates"},indent=2))
    print("Certificate cases:",report["certificates"]["cases"])
    print("Residuals:",report["certificates"]["maximum_absolute_residuals"])


if __name__ == "__main__":
    main()
