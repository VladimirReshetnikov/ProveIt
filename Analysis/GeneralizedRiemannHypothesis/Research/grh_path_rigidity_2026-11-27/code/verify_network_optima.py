#!/usr/bin/env python3
"""Reproducible checks for network_optima.tex.

The proof is analytic. These exact and floating-point checks independently
check constants, matrix order, the explicit edge integral, and both stability
identities. Dependencies: numpy, scipy, sympy. No network access is used.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import scipy
from scipy.integrate import quad
from scipy.linalg import eigh
import sympy as sp


def exact_three_vertex_example() -> dict:
    d = sp.Matrix([1, 1, 4])
    C = sp.diag(1, 1, 4) - d * d.T / 6
    u, v = sp.Matrix([1, -1, 0]), sp.Matrix([1, 1, -2])
    sqrtC = u * u.T / 2 + sp.sqrt(2) * v * v.T / 6
    assert sp.simplify(sqrtC * sqrtC - C) == sp.zeros(3)
    assert sqrtC * sp.ones(3, 1) == sp.zeros(3, 1)
    Linf = 2 * C / 3
    Lmean = 2 * sqrtC / (1 + sp.sqrt(2))
    assert sp.trace(Linf) == 2
    assert sp.simplify(sp.trace(Lmean) - 2) == 0
    assert -Linf[0, 1] == sp.Rational(1, 9)
    assert -Linf[0, 2] == sp.Rational(4, 9)
    assert sp.simplify(-Lmean[0, 1] - (3-sp.sqrt(2))/(3*(1+sp.sqrt(2)))) == 0
    assert sp.simplify(-Lmean[0, 2] - 2*sp.sqrt(2)/(3*(1+sp.sqrt(2)))) == 0
    return {
        "degrees": [1, 1, 4],
        "budget": 1,
        "positive_eigenvalues_C": [1, 2],
        "worst_optimum": "3/2",
        "sum_optimum": "(3+2*sqrt(2))/2",
        "minimax_edges_12_13_23": ["1/9", "4/9", "4/9"],
        "mean_edges_12_13_23": [str(sp.simplify(-Lmean[i,j])) for i,j in [(0,1),(0,2),(1,2)]],
        "exact_symbolic_checks": "passed",
    }


def on_zero_sum(n: int) -> np.ndarray:
    """Orthonormal n by (n-1) basis, avoiding the Laplacian null direction."""
    Q, _ = np.linalg.qr(np.vstack([np.eye(n-1), -np.ones((1,n-1))]))
    return Q


def matrix_power_spd(A: np.ndarray, p: float) -> np.ndarray:
    vals, vecs = np.linalg.eigh(A)
    assert vals.min() > 0
    return (vecs * vals**p) @ vecs.T


def nuclear_symmetric(A: np.ndarray) -> float:
    return float(np.abs(np.linalg.eigvalsh((A+A.T)/2)).sum())


def numerical_checks(seed: int = 20261127, count: int = 240) -> dict:
    rng = np.random.default_rng(seed)
    errors = {"optimum": 0.0, "residual_identity": 0.0,
              "mean_stationarity": 0.0, "spectral_reduction": 0.0}
    contrast_checks = 0
    for trial in range(count):
        n = 2 + trial % 9
        degrees = rng.integers(1, 100, n).astype(float)
        budget = float(rng.integers(1, 20)) / 3
        b = 2 * budget
        N = float(degrees.sum())
        C = np.diag(degrees) - np.outer(degrees,degrees)/N
        Q = on_zero_sum(n)
        CH = Q.T @ C @ Q
        sqrtCH = matrix_power_spd(CH, .5)
        sqrtC = Q @ sqrtCH @ Q.T
        T, S = float(np.trace(CH)), float(np.trace(sqrtCH))
        Linf = b*C/T
        Lmean = b*sqrtC/S
        for Lopt in [Linf,Lmean]:
            assert np.max(np.abs(Lopt @ np.ones(n))) < 1e-10*b
            assert np.all(Lopt[np.triu_indices(n,1)] < 0)
            assert np.isclose(np.trace(Lopt), b)
        LinfH, LmeanH = Q.T @ Linf @ Q, Q.T @ Lmean @ Q
        t_opt = float(eigh(CH,LinfH,eigvals_only=True).max())
        f_opt = float(np.trace(np.linalg.solve(LmeanH,CH)))
        errors["optimum"] = max(errors["optimum"],abs(t_opt-T/b)/(T/b),abs(f_opt-S*S/b)/(S*S/b))
        assert np.isclose(t_opt,T/b,rtol=1e-10)
        assert np.isclose(f_opt,S*S/b,rtol=1e-10)

        # Independently, the first derivative of the mean objective is equal
        # for every edge at the proposed optimizer.
        invmean = np.linalg.inv(LmeanH)
        derivative_kernel = Q @ invmean @ CH @ invmean @ Q.T
        for i in range(n):
            for j in range(i+1,n):
                derivative = derivative_kernel[i,i] + derivative_kernel[j,j] - 2*derivative_kernel[i,j]
                expected = 2*(S/b)**2
                errors["mean_stationarity"] = max(errors["mean_stationarity"],abs(derivative/expected-1))
                assert np.isclose(derivative,expected,rtol=1e-10)

        # The tested competitors have either complete support or a spanning
        # path plus a random selection of the other edges.
        w = np.triu(rng.exponential(1, (n,n)),1)
        if trial % 2:
            for i in range(n):
                for j in range(i+2,n):
                    if rng.random() < .65: w[i,j] = 0
        w += w.T
        w *= budget / np.triu(w,1).sum()
        L = np.diag(w.sum(axis=1)) - w
        LH = Q.T @ L @ Q
        t = float(eigh(CH,LH,eigvals_only=True).max())
        F = float(np.trace(np.linalg.solve(LH,CH)))
        t_alt = float(np.linalg.eigvalsh(sqrtCH @ np.linalg.solve(LH,sqrtCH)).max())
        errors["spectral_reduction"] = max(errors["spectral_reduction"],abs(t_alt/t-1))
        assert t >= T/b*(1-1e-10)
        assert F >= S*S/b*(1-1e-10)
        assert np.isclose(t,t_alt,rtol=1e-10)
        assert np.linalg.eigvalsh(t*LH-CH).min() >= -1e-8*max(1,T)

        eta = max(0,t/(T/b)-1)
        diff = L-Linf
        assert nuclear_symmetric(diff) <= 2*b*eta/(1+eta)+1e-8*b
        assert np.abs(np.linalg.eigvalsh(diff)).max() <= b*eta/(1+eta)+1e-8*b

        invsqrtL = matrix_power_spd(LH,-.5)
        residual = (S/b)**2 * np.linalg.norm(invsqrtL @ (LH-LmeanH),"fro")**2
        gap = F-S*S/b
        errors["residual_identity"] = max(errors["residual_identity"],abs(residual-gap)/max(1,F))
        assert np.isclose(residual,gap,rtol=1e-9,atol=1e-10)
        epsilon = max(0,F/(S*S/b)-1)
        assert nuclear_symmetric(L-Lmean) <= b*np.sqrt(epsilon)+1e-8*b

        for i in range(n):
            for j in range(n):
                for k in range(j):
                    if i in (j,k) or degrees[j] <= degrees[k]: continue
                    ratio = Lmean[i,j]/Lmean[i,k]
                    assert 1-1e-10 < ratio < degrees[j]/degrees[k]+1e-10
                    contrast_checks += 1
    return {"random_seed":seed,"competitor_graphs":count,
            "vertex_counts":list(range(2,11)),"contrast_checks":contrast_checks,
            "maximum_relative_errors":errors,"status":"passed"}


def integral_checks() -> dict:
    d = np.array([1.,2.,5.,9.]); n=len(d); N=d.sum()
    C=np.diag(d)-np.outer(d,d)/N
    Q=on_zero_sum(n)
    sqrtC=Q @ matrix_power_spd(Q.T @ C @ Q,.5) @ Q.T
    checks=[]
    for i in range(n):
        for j in range(i+1,n):
            # t=u^2 removes the integrable singularity at t=0.
            def integrand(u):
                t=u*u
                h=np.sum(d/(t+d))
                return 2*d[i]*d[j]/(np.pi*(t+d[i])*(t+d[j])*h)
            integral,err=quad(integrand,0,np.inf,epsabs=1e-12,epsrel=1e-12)
            expected=-sqrtC[i,j]
            assert np.isclose(integral,expected,rtol=1e-10,atol=1e-11)
            checks.append({"edge":[i+1,j+1],"integral":integral,
                           "negative_sqrt_entry":float(expected),
                           "quadrature_error_estimate":err})
    return {"degrees":d.tolist(),"edges":checks,"status":"passed"}


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path("network_verification.json"))
    args=parser.parse_args()
    result={"claim":"Checks, not a substitute for the analytic proofs",
            "versions":{"numpy":np.__version__,"scipy":scipy.__version__,"sympy":sp.__version__},
            "exact_example":exact_three_vertex_example(),
            "numerical":numerical_checks(),"edge_integrals":integral_checks()}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"passed","graphs":result["numerical"]["competitor_graphs"],
                      "contrasts":result["numerical"]["contrast_checks"],"output":str(args.output)}))


if __name__=="__main__": main()
