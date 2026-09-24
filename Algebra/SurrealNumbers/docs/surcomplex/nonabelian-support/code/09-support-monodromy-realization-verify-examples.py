#!/usr/bin/env python3
"""Finite checks for Global Hahn Support and Surcomplex Riemann--Hilbert.

Exact algebra uses SymPy. Numerical tests integrate coefficient equations,
not a numerical surrogate for an infinite or infinitesimal Hahn monomial.
These checks are not a formal verification of the general theorems.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Callable

import numpy as np
import scipy
from scipy.integrate import solve_ivp
import sympy as sp


def exact_checks() -> dict:
    u, v = sp.symbols("u v")
    X = sp.Matrix([[0, 1], [0, 0]])
    Y = sp.Matrix([[0, 0], [1, 0]])
    I = sp.eye(2)
    H = X * Y - Y * X
    M0, M1 = I + u * X, I + v * Y
    C = sp.expand(M0 * M1 * (I - u * X) * (I - v * Y))
    expected = sp.Matrix([[1 + u*v + u*u*v*v, -u*u*v],
                          [u*v*v, 1-u*v]])
    checks = {
        "X_squared_zero": X**2 == sp.zeros(2),
        "Y_squared_zero": Y**2 == sp.zeros(2),
        "commutator_H": H == sp.diag(1, -1),
        "target_0_determinant_one": sp.expand(M0.det()) == 1,
        "target_1_determinant_one": sp.expand(M1.det()) == 1,
        "exact_group_commutator": sp.simplify(C-expected) == sp.zeros(2),
        "group_commutator_determinant_one": sp.expand(C.det()) == 1,
        "mixed_correction_traceless": H.trace() == 0,
    }
    assert all(checks.values()), checks
    return {"checks": checks, "commutator": str(C)}


Degree = tuple[int, int]
DEGREES: list[Degree] = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
INDEX = {degree: i for i, degree in enumerate(DEGREES)}
X = np.array([[0, 1], [0, 0]], dtype=complex)
Y = np.array([[0, 0], [1, 0]], dtype=complex)
H = X @ Y - Y @ X
C = np.log(2) / (2j*np.pi)


def segment(a: complex, b: complex) -> Callable[[float], tuple[complex, complex]]:
    return lambda s: (a + (b-a)*s, b-a)


def circle(center: complex, radius: float, phase: float
           ) -> Callable[[float], tuple[complex, complex]]:
    def point(s: float) -> tuple[complex, complex]:
        displacement = radius * np.exp(1j*(phase + 2*np.pi*s))
        return center + displacement, 2j*np.pi*displacement
    return point


def holonomy_coefficients(puncture: int, corrected: bool) -> np.ndarray:
    if puncture == 0:
        parts = [segment(.5, .25), circle(0, .25, 0), segment(.25, .5)]
    elif puncture == 1:
        parts = [segment(.5, .75), circle(1, .25, np.pi), segment(.75, .5)]
    else:
        raise ValueError("The example has only punctures 0 and 1.")
    state = np.zeros((len(DEGREES), 2, 2), dtype=complex)
    state[0] = np.eye(2)
    for path in parts:
        def rhs(s: float, flat: np.ndarray) -> np.ndarray:
            z, dz = path(s)
            eta0 = dz/(2j*np.pi*z)
            eta1 = dz/(2j*np.pi*(z-1))
            A: dict[Degree, np.ndarray] = {(1, 0): X*eta0, (0, 1): Y*eta1}
            if corrected:
                A[(1, 1)] = -C*H*(eta0-eta1)
            current = flat.reshape(state.shape)
            deriv = np.zeros_like(current)
            for degree, k in INDEX.items():
                for delta, coeff in A.items():
                    previous = (degree[0]-delta[0], degree[1]-delta[1])
                    if previous in INDEX:
                        deriv[k] += coeff @ current[INDEX[previous]]
            return deriv.ravel()
        solution = solve_ivp(rhs, (0, 1), state.ravel(), method="DOP853",
                             rtol=2e-12, atol=2e-13)
        if not solution.success:
            raise RuntimeError(solution.message)
        state = solution.y[:, -1].reshape(state.shape)
    return state


def numerical_checks() -> dict:
    results = {}
    for puncture in (0, 1):
        raw = holonomy_coefficients(puncture, False)
        corrected = holonomy_coefficients(puncture, True)
        expected_raw_mixed = (1 if puncture == 0 else -1)*C*H
        expected = np.zeros_like(corrected)
        expected[0] = np.eye(2)
        expected[INDEX[(1, 0)]] = X if puncture == 0 else np.zeros((2, 2))
        expected[INDEX[(0, 1)]] = Y if puncture == 1 else np.zeros((2, 2))
        raw_error = float(np.max(np.abs(raw[INDEX[(1, 1)]]-expected_raw_mixed)))
        corrected_error = float(np.max(np.abs(corrected-expected)))
        assert raw_error < 2e-9, (puncture, "raw", raw_error)
        assert corrected_error < 2e-9, (puncture, "corrected", corrected_error)
        results[f"meridian_{puncture}"] = {
            "uncorrected_mixed_formula_max_error": raw_error,
            "corrected_degree_at_most_two_max_error": corrected_error,
            "uncorrected_mixed_00": {
                "real": float(raw[INDEX[(1, 1)], 0, 0].real),
                "imag": float(raw[INDEX[(1, 1)], 0, 0].imag),
            },
        }
    return results


def main() -> None:
    result = {
        "status": "all checks passed",
        "scope": "Eight exact algebra checks and four coefficient-ODE error checks; not formal theorem verification.",
        "versions": {"numpy": np.__version__, "scipy": scipy.__version__,
                     "sympy": sp.__version__},
        "exact": exact_checks(),
        "numerical": numerical_checks(),
    }
    text = json.dumps(result, indent=2)
    print(text)
    Path(__file__).with_name("verification_results.json").write_text(text+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
