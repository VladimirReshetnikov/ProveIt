#!/usr/bin/env python3
"""Independent numerical checks of the centered cube expansion on odd groups.

For each of C3, C3 x C3, C5, C7, C9, and C15, form a real centered
function using the fixed PCG64 seed below.  Exhaust all physical cube
parameters, expand the eight-factor product as a polynomial in its
constant term, and compare every coefficient with the Fourier formulas.
The physical calculation does not use the Fourier cube identity.

This is finite floating-point verification, not a proof for arbitrary
groups or arbitrary functions.  All coefficient identities are proved
in the accompanying manuscript.  Dependency: numpy.

Run from any working directory:
    python3 code/verify_odd_cube_expansion.py

The full report is written relative to the project directory, in
data/odd_cube_expansion_checks.json.
"""
from itertools import product
from pathlib import Path
import json

import numpy as np


SEED = 612741


class Group:
    """A product of explicitly specified cyclic groups."""
    def __init__(self, moduli):
        self.moduli = np.array(moduli, dtype=int)
        self.points = np.array(list(product(*(range(m) for m in moduli))),
                               dtype=int)
        self.n = len(self.points)
        index = {tuple(x): i for i, x in enumerate(self.points)}
        self.add = np.array([[index[tuple((x + y) % self.moduli)]
                             for y in self.points] for x in self.points])
        self.neg = np.array([index[tuple(-x % self.moduli)]
                             for x in self.points])
        self.sub = self.add[:, self.neg]
        self.double = self.add[np.arange(self.n), np.arange(self.n)]

    def transform(self, f):
        pairings = (self.points / self.moduli) @ self.points.T
        return np.exp(-2j * np.pi * pairings) @ f / self.n


def physical_coefficients(G, f):
    """Return all coefficients of E_cube product(delta + f(vertex)).

Entry j is the coefficient of delta^(8-j).  Elementary symmetric
polynomials are accumulated directly on the eight physical values.
Every ordered tuple (x,h1,h2,h3) is included, including repetitions.
"""
    tuples = np.array(list(product(range(G.n), repeat=4)), dtype=int)
    x, h1, h2, h3 = tuples.T
    coefficients = [np.ones(len(x))] + [np.zeros(len(x)) for _ in range(8)]
    for count, bits in enumerate(product(range(2), repeat=3)):
        vertex = x.copy()
        for bit, step in zip(bits, (h1, h2, h3)):
            if bit:
                vertex = G.add[vertex, step]
        value = f[vertex]
        # Descending update preserves the preceding elementary coefficients.
        for j in range(count + 1, 0, -1):
            coefficients[j] += value * coefficients[j - 1]
    return np.array([c.mean() for c in coefficients])


def fourier_coefficients(G, a):
    """Evaluate B5, H, J, K, C7 and the Fourier square sum independently."""
    lam = np.abs(a) ** 2
    S = float(np.sum(lam ** 2))
    B5 = np.sum(a[G.double] * np.conj(a) ** 3 * a)
    H = float(np.sum(lam[:, None] * lam[None, :] * lam[G.neg[G.add]]))
    J = np.sum(lam[:, None] * a[None, :] ** 2 *
               a[G.sub] * np.conj(a[G.add]))
    K = np.sum(a[:, None] ** 2 * a[None, :] ** 2 *
               a[G.neg[G.add]] ** 2)
    T = np.empty((G.n, G.n), dtype=complex)
    for s in range(G.n):
        T[s] = np.sum(a[None, :] * np.conj(a[G.add[s]])[None, :] *
                      np.conj(a[G.add]) * a[G.add[s, G.add]], axis=1)
    L = (2 * np.real(a[:, None] * a[None, :] * np.conj(a[G.add])) +
         2 * np.real(a[:, None] * np.conj(a[None, :]) * np.conj(a[G.sub])))
    C6 = float((12 * H + 12 * J + 4 * K).real)
    C7 = float(2 * np.vdot(T, L).real)
    U3_power8 = float(np.sum(np.abs(T) ** 2))
    expected = np.array([1., 0., 0., 0., 12 * S, 8 * B5.real,
                         C6, C7, U3_power8])
    stats = {"S": S, "B5": float(B5.real), "H": H,
             "J": float(J.real), "K": float(K.real),
             "C6": C6, "C7": C7, "U3_power8": U3_power8,
             "largest_reality_residual": float(max(abs(B5.imag),
                  abs(J.imag), abs(K.imag), np.max(np.abs(T.imag))))}
    return expected, stats


def main():
    rng = np.random.Generator(np.random.PCG64(SEED))
    cases = []
    for name, moduli in (("C3", (3,)), ("C3 x C3", (3, 3)),
                         ("C5", (5,)), ("C7", (7,)),
                         ("C9", (9,)), ("C15", (15,))):
        G = Group(moduli)
        f = rng.normal(size=G.n)
        f -= f.mean()
        a = G.transform(f)
        a[0] = 0  # Enforce centering in the floating-point Fourier presentation.
        physical = physical_coefficients(G, f)
        expected, stats = fourier_coefficients(G, a)
        residuals = np.abs(physical - expected)
        error = float(np.max(residuals))
        if error >= 1e-10:
            raise ArithmeticError(f"Coefficient mismatch for {name}: {error}")
        cases.append({
            "group": name, "cyclic_moduli": list(moduli),
            "group_order": G.n, "physical_cubes_exhausted": G.n ** 4,
            "real_centered_function_values": f.tolist(),
            "mean_roundoff_residual": float(abs(f.mean())),
            "coefficients": [
                {"number_of_centered_factors": j,
                 "power_of_constant_delta": 8 - j,
                 "direct_physical_coefficient": float(physical[j]),
                 "fourier_formula_coefficient": float(expected[j]),
                 "absolute_residual": float(residuals[j])}
                for j in range(9)],
            "fourier_statistics": stats,
            "largest_absolute_coefficient_residual": error,
        })
    report = {
        "status": "all six finite numerical checks passed",
        "verification_type": "floating-point finite examples, not a universal proof",
        "random_generator": "numpy.random.PCG64", "seed": SEED,
        "numpy_version": np.__version__,
        "normalization": "spatial and Fourier-transform averages normalized; frequency sums unnormalized",
        "coefficient_convention": "entry j is the coefficient of delta^(8-j) in the centered cube expansion",
        "absolute_tolerance": 1e-10,
        "total_physical_cubes_exhausted": sum(c["physical_cubes_exhausted"] for c in cases),
        "largest_absolute_coefficient_residual": max(
            c["largest_absolute_coefficient_residual"] for c in cases),
        "cases": cases,
    }
    destination = (Path(__file__).resolve().parents[1] / "data" /
                   "odd_cube_expansion_checks.json")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "report": str(destination),
                      "physical_cubes": report["total_physical_cubes_exhausted"],
                      "largest_coefficient_residual":
                          report["largest_absolute_coefficient_residual"]}, indent=2))


if __name__ == "__main__":
    main()
