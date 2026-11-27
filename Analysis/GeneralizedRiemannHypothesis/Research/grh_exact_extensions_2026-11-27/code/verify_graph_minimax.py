#!/usr/bin/env python3
"""Exact certificates and numerical diagnostics for graph zero-transport minimax.

The theorem is proved in graph_minimax_notes.md. These computations check the
normalizations, an unequal-degree example, the forest/compression identity, and
the asserted inequalities on deterministic random inputs. Floating-point
diagnostics are not substitutes for the proof.

Dependencies: Python 3, numpy, sympy.
Usage: python verify_graph_minimax.py --output graph_verification.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import sympy as sp


def laplacian(weights: np.ndarray) -> np.ndarray:
    return np.diag(weights.sum(axis=1)) - weights


def psd_power(matrix: np.ndarray, exponent: float) -> np.ndarray:
    vals, vecs = np.linalg.eigh(matrix)
    scale = max(1.0, float(np.max(np.abs(vals))))
    vals = np.where(vals > 1e-12 * scale, vals, 0.0)
    return (vecs * vals**exponent) @ vecs.T


def pinv_laplacian(matrix: np.ndarray) -> np.ndarray:
    n = len(matrix)
    j = np.ones((n, n)) / n
    return np.linalg.inv(matrix + j) - j


def matrix_cost(C: np.ndarray, L: np.ndarray, p: float, N: int) -> float:
    Chalf = psd_power(C, 0.5)
    B = Chalf @ pinv_laplacian(L) @ Chalf
    vals = np.maximum(np.linalg.eigvalsh(B), 0.0)
    if math.isinf(p):
        return float(vals[-1])
    return float((sum(vals**p) / (N - 1)) ** (1.0 / p))


def optimizer(degrees: np.ndarray, p: float, budget: float = 1.0):
    N = int(sum(degrees))
    C = np.diag(degrees) - np.outer(degrees, degrees) / N
    r = 1.0 if math.isinf(p) else p / (p + 1.0)
    Cr = psd_power(C, r)
    S = float(np.trace(Cr))
    L = 2 * budget * Cr / S
    value = S / (2 * budget) if math.isinf(p) else (
        S ** (1 + 1 / p) / (2 * budget * (N - 1) ** (1 / p))
    )
    return C, L, value


def exact_certificates():
    z = sp.Symbol("z")
    s = sp.sqrt(6) / 2
    d = sp.Matrix([1, 1, 2])
    C = sp.diag(1, 1, 2) - d * d.T / 4
    a = sp.Matrix([1, -1, 0])
    b = sp.Matrix([1, 1, -2])
    Pa = a * a.T / 2
    Pb = b * b.T / 6
    assert C == Pa + sp.Rational(3, 2) * Pb
    assert C.eigenvals() == {0: 1, 1: 1, sp.Rational(3, 2): 1}
    C_half = Pa + s * Pb
    assert sp.simplify(C_half * C_half - C) == sp.zeros(3)
    L1 = 2 * C_half / (1 + s)
    Linf = sp.Rational(4, 5) * C
    assert Linf == sp.Matrix([[sp.Rational(3, 5), -sp.Rational(1, 5), -sp.Rational(2, 5)],
                             [-sp.Rational(1, 5), sp.Rational(3, 5), -sp.Rational(2, 5)],
                             [-sp.Rational(2, 5), -sp.Rational(2, 5), sp.Rational(4, 5)]])
    assert sp.simplify(L1.trace() - 2) == 0
    mean1 = sp.simplify((1 + s)**2 / 6)
    assert sp.simplify(mean1 - (5 + 2 * sp.sqrt(6)) / 12) == 0
    max1 = sp.simplify(s * (1 + s) / 2)
    assert sp.simplify(max1 - (3 + sp.sqrt(6)) / 4) == 0

    def forest(P, w12, w13, w23):
        tau = w12*w13 + w12*w23 + w13*w23
        ans = sp.prod(sp.diff(x, z) for x in P)
        ans += w12 * sp.diff(P[0]*P[1], z) * sp.diff(P[2], z)
        ans += w13 * sp.diff(P[0]*P[2], z) * sp.diff(P[1], z)
        ans += w23 * sp.diff(P[1]*P[2], z) * sp.diff(P[0], z)
        ans += tau * sp.diff(sp.prod(P), z)
        return sp.expand(ans), tau

    collapsed_inf, tau_inf = forest([z, z, z*z], sp.Rational(1,5), sp.Rational(2,5), sp.Rational(2,5))
    assert sp.factor(collapsed_inf) == sp.Rational(2,25)*z*(4*z+5)**2
    x = (3-s)/(3*(1+s))
    y = 2*s/(3*(1+s))
    collapsed1, tau1 = forest([z,z,z*z], x,y,y)
    target1 = 4*tau1*z*(z+(1+s)/2)*(z+s*(1+s)/2)
    assert sp.simplify(collapsed1-target1) == 0

    # An exact noncollapsed forest/compression identity with integer roots.
    roots = [sp.Integer(0),sp.Integer(1),sp.Integer(-1),sp.Integer(2)]
    P = [z,z-1,(z+1)*(z-2)]
    F, _ = forest(P, sp.Rational(1,5), sp.Rational(2,5), sp.Rational(2,5))
    V = sp.Matrix([[1,0,0],[0,1,0],[0,0,1],[0,0,1]])
    block = (z*sp.eye(4)-sp.diag(*roots)).row_join(V)
    block = block.col_join((-V.T).row_join(Linf))
    assert sp.expand(block.det()-F) == 0

    # An exact mean-error stability certificate against a rational competitor.
    J = sp.ones(3)/3
    L_uniform = sp.eye(3)-J   # each edge is 1/3, budget is 1
    Linv = L_uniform          # this particular projector is its pseudoinverse
    Delta = L_uniform-L1
    f = sp.trace(C*Linv)
    fstar = 3*mean1
    relative = sp.simplify(f/fstar-1)
    certificate = sp.simplify(sp.trace(Delta*Linv*Delta)/2)
    assert sp.simplify(relative-certificate) == 0

    return {
        "degrees": [1,1,2],
        "budget": "1",
        "C_positive_eigenvalues": ["1","3/2"],
        "p1_edges": [str(sp.simplify(x)),str(sp.simplify(y)),str(sp.simplify(y))],
        "pinfinity_edges": ["1/5","2/5","2/5"],
        "p1_optimal_mean": str(mean1),
        "pinfinity_optimal_maximum": "5/4",
        "pinfinity_graph_mean": "5/6",
        "p1_graph_maximum": str(max1),
        "collapsed_pinfinity_forest": str(sp.factor(collapsed_inf)),
        "noncollapsed_forest": str(F),
        "mean_gap_for_uniform_competitor": str(relative),
        "exact_checks_passed": 11,
    }


def numerical_diagnostics():
    rng = np.random.default_rng(20261127)
    case_count = 0
    graph_comparisons = 0
    root_comparisons = 0
    worst_optimizer_relative_error = 0.0
    worst_cost_underflow = 0.0
    worst_root_bound_excess = 0.0
    worst_collapsed_error = 0.0
    worst_stability_error = 0.0
    minimum_optimal_edge = math.inf
    for n in range(2,7):
        for _ in range(3):
            degrees = rng.integers(1,5,size=n)
            N = int(sum(degrees))
            V = np.zeros((N,n))
            start = 0
            for i,di in enumerate(degrees):
                V[start:start+di,i] = 1
                start += di
            # A fixed orthonormal basis of 1_N^perp.
            raw_basis = np.eye(N)[:,:N-1]
            raw_basis[-1,:] = -1
            U,_ = np.linalg.qr(raw_basis,mode="reduced")
            for p in [1.0,1.5,2.0,4.0,math.inf]:
                C,Lstar,predicted = optimizer(degrees,p)
                actual = matrix_cost(C,Lstar,p,N)
                worst_optimizer_relative_error = max(worst_optimizer_relative_error,abs(actual/predicted-1))
                minimum_optimal_edge = min(minimum_optimal_edge,float(np.min(-Lstar[np.triu_indices(n,1)])))
                assert np.max(np.abs(Lstar.sum(axis=1))) < 1e-11
                assert abs(np.trace(Lstar)-2) < 1e-11
                assert np.min(-Lstar[np.triu_indices(n,1)]) > 0
                case_count += 1
                for trial in range(10):
                    W = np.zeros((n,n))
                    W[np.triu_indices(n,1)] = rng.uniform(0.05,1.0,size=n*(n-1)//2)
                    W += W.T
                    W /= np.sum(W)/2
                    L = laplacian(W)
                    candidate = matrix_cost(C,L,p,N)
                    worst_cost_underflow = max(worst_cost_underflow,1-candidate/predicted)
                    graph_comparisons += 1
                    if p==1:
                        Delta = L-Lstar
                        relative = candidate/predicted-1
                        certificate = np.trace(Delta@pinv_laplacian(L)@Delta)/2
                        worst_stability_error = max(worst_stability_error,abs(relative-certificate))
                    if trial>=2:
                        continue
                    roots = rng.normal(size=N)
                    A = U.T@np.diag(roots)@U
                    B = U.T@V@pinv_laplacian(L)@V.T@U
                    beta = np.linalg.eigvalsh(A)
                    lam = np.linalg.eigvalsh(A-B)
                    shifts = beta-lam
                    assert np.min(shifts) > -1e-9
                    observed = float(np.max(shifts)) if math.isinf(p) else float(np.mean(np.maximum(shifts,0)**p)**(1/p))
                    worst_root_bound_excess = max(worst_root_bound_excess,observed/candidate-1)
                    # All input roots zero attain the stated supremum.
                    bvals = np.maximum(np.linalg.eigvalsh(B),0)
                    collapsed = float(np.max(bvals)) if math.isinf(p) else float(np.mean(bvals**p)**(1/p))
                    worst_collapsed_error = max(worst_collapsed_error,abs(collapsed/candidate-1))
                    root_comparisons += 1
    assert worst_optimizer_relative_error < 1e-9
    assert worst_cost_underflow < 1e-9
    assert worst_root_bound_excess < 1e-9
    assert worst_collapsed_error < 1e-9
    assert worst_stability_error < 1e-9
    return {
        "seed": 20261127,
        "optimizer_cases": case_count,
        "competing_graph_comparisons": graph_comparisons,
        "noncollapsed_and_collapsed_root_cases": root_comparisons,
        "largest_optimizer_relative_error": worst_optimizer_relative_error,
        "largest_competing_cost_underflow": worst_cost_underflow,
        "largest_zero_displacement_bound_excess": worst_root_bound_excess,
        "largest_collapsed_equality_relative_error": worst_collapsed_error,
        "largest_stability_identity_absolute_error": worst_stability_error,
        "smallest_optimal_edge_in_cases": minimum_optimal_edge,
        "status": "passed; floating-point diagnostics only",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path("graph_verification.json"))
    args = parser.parse_args()
    result = {"exact":exact_certificates(),"numerical":numerical_diagnostics()}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
