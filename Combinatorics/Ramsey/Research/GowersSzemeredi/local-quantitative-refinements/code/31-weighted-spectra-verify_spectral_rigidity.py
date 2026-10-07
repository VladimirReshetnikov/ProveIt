#!/usr/bin/env python3
"""Finite numerical diagnostics for sharp local spectral rigidity.

This is supplementary evidence, not a proof or a Lean verification. The exact
C2 polynomial identity is checked with Fraction arithmetic. All other checks
use complex128 arithmetic and report their largest observed residuals.

Run: python3 code/verify_spectral_rigidity.py
Requires: Python 3 and NumPy.
"""

from __future__ import annotations

import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np


TOL = 3e-10
SEED = 20261006


class AbelianGroup:
    def __init__(self, moduli):
        self.moduli = tuple(moduli)
        self.points = list(itertools.product(*(range(n) for n in moduli)))
        self.index = {x: i for i, x in enumerate(self.points)}
        self.n = len(self.points)
        self.zero = (0,) * len(moduli)
        self.phase_points = list(itertools.product(self.points, self.points))
        self.phase_index = {x: i for i, x in enumerate(self.phase_points)}
        self.minus = np.array(
            [[self.index[self.sub(x, h)] for x in self.points]
             for h in self.points], dtype=int
        )
        self.characters = np.array(
            [[self.character(xi, x) for x in self.points]
             for xi in self.points], dtype=complex
        )

    def add(self, a, b):
        return tuple((x + y) % n for x, y, n in zip(a, b, self.moduli))

    def sub(self, a, b):
        return tuple((x - y) % n for x, y, n in zip(a, b, self.moduli))

    def character(self, xi, x):
        angle = sum(a * b / n for a, b, n in zip(xi, x, self.moduli))
        return np.exp(2j * np.pi * angle)

    def phase_sub(self, a, b):
        return self.sub(a[0], b[0]), self.sub(a[1], b[1])

    def phase_add(self, a, b):
        return self.add(a[0], b[0]), self.add(a[1], b[1])

    def beta(self, a, b):
        return self.character(a[1], b[0]) / self.character(b[1], a[0])

    def weyl(self, u, v):
        h, xi = u
        return self.characters[self.index[xi]] * v[self.minus[self.index[h]]]

    def profile(self, v):
        return np.array(
            [abs(np.vdot(v, self.weyl(u, v))) ** 2
             for u in self.phase_points], dtype=float
        )

    def symplectic_transform(self, q):
        return np.array(
            [sum(self.beta(v, u) * q[j]
                 for j, u in enumerate(self.phase_points)) / self.n
             for v in self.phase_points], dtype=complex
        )

    def cube_kappa(self, v):
        # v has counting-measure norm1, while the article's f=sqrt(N)*v.
        # The four average factors and eight sqrt(N) factors cancel.
        total = 0j
        for x, a, b, c in itertools.product(self.points, repeat=4):
            product = 1 + 0j
            for bits in itertools.product((0, 1), repeat=3):
                y = x
                for bit, direction in zip(bits, (a, b, c)):
                    if bit:
                        y = self.add(y, direction)
                value = v[self.index[y]]
                product *= value.conjugate() if sum(bits) % 2 else value
            total += product
        return total

    def twirl(self, v, subgroup):
        rho = np.zeros((self.n, self.n), dtype=complex)
        for u in subgroup:
            wv = self.weyl(u, v)
            rho += np.outer(wv, wv.conjugate())
        return rho / len(subgroup)


def normalized(z):
    return z / np.linalg.norm(z)


def local_defect(t):
    return 4 * t * (1 - t) * (1 - 2 * t) ** 2


def inverse_defect(delta):
    return (1 - math.sqrt((1 + math.sqrt(1 - 4 * delta)) / 2)) / 2


def exact_c2_checks():
    rows = []
    for t in [Fraction(0), Fraction(1, 10000), Fraction(1, 1000),
              Fraction(1, 100), Fraction(1, 10), Fraction(1, 8)]:
        f = 1 - t
        profile = [Fraction(1), (1 - 2 * t) ** 2, 4 * f * t, Fraction(0)]
        kappa = sum(x * x for x in profile) / 2
        envelope = f ** 4 + 14 * f * f * t * t + t ** 4
        defect = 4 * t * (1 - t) * (1 - 2 * t) ** 2
        assert kappa == envelope and 1 - kappa == defect
        rows.append({"t": str(t), "kappa": str(kappa),
                     "delta": str(defect), "identity_exact": True})
    return rows


def coset_quadratic_state(group, steps, offset):
    """A quadratic phase on a rectangular subgroup coset of product cyclics."""
    v = np.zeros(group.n, dtype=complex)
    for i, x in enumerate(group.points):
        y = group.sub(x, offset)
        if all(a % step == 0 for a, step in zip(y, steps)):
            coordinates = [a // step for a, step in zip(y, steps)]
            sizes = [n // step for n, step in zip(group.moduli, steps)]
            phase = sum((j + 1) * a * a / n
                        for j, (a, n) in enumerate(zip(coordinates, sizes)))
            phase += sum((j + 2) * a / n
                         for j, (a, n) in enumerate(zip(x, group.moduli)))
            v[i] = np.exp(2j * np.pi * phase)
    return normalized(v)


def verify():
    rng = np.random.default_rng(SEED)
    summary = {
        "seed": SEED,
        "purpose": "Numerical diagnostics; not a mathematical proof",
        "tolerance": TOL,
        "exact_c2": exact_c2_checks(),
        "groups": [],
        "near_coset_examples": [],
        "nonisotropic_twirl_examples": [],
    }
    groups = [(2,), (3,), (4,), (5,), (6,), (2, 2), (2, 4), (3, 3), (2, 6)]
    residuals = {"moyal": 0.0, "self_duality": 0.0, "cube_identity": 0.0,
                 "twirl_identity": 0.0, "envelope_violation": 0.0,
                 "inverse_bound_violation": 0.0}
    for moduli in groups:
        group = AbelianGroup(moduli)
        v = normalized(rng.normal(size=group.n) + 1j * rng.normal(size=group.n))
        q = group.profile(v)
        kappa = float(np.sum(q * q) / group.n)
        moyal_error = abs(float(q.sum()) - group.n)
        dual_error = float(np.max(np.abs(group.symplectic_transform(q) - q)))
        residuals["moyal"] = max(residuals["moyal"], moyal_error)
        residuals["self_duality"] = max(residuals["self_duality"], dual_error)
        assert moyal_error < TOL and dual_error < TOL
        cube_error = None
        if group.n <= 6:
            cube_error = float(abs(group.cube_kappa(v) - kappa))
            residuals["cube_identity"] = max(residuals["cube_identity"], cube_error)
            assert cube_error < TOL
        summary["groups"].append({"moduli": list(moduli), "N": group.n,
                                  "moyal_error": moyal_error,
                                  "self_duality_error": dual_error,
                                  "cube_identity_error": cube_error})

        # The full phase space is non-isotropic and twirls to I/N.
        rho = group.twirl(v, group.phase_points)
        purity = float(np.trace(rho @ rho).real)
        twirl_error = abs(purity - float(q.mean()))
        residuals["twirl_identity"] = max(residuals["twirl_identity"], twirl_error)
        assert twirl_error < TOL and purity <= 0.5 + TOL
        assert np.max(np.abs(rho - np.eye(group.n) / group.n)) < TOL
        summary["nonisotropic_twirl_examples"].append({
            "moduli": list(moduli), "purity": purity,
            "upper_bound": 0.5, "exact_expected_purity": 1 / group.n})

        # Vary both support and phase. Each rectangular K may be proper or full.
        choices = [tuple(1 for _ in moduli),
                   tuple(2 if n % 2 == 0 else n for n in moduli)]
        for steps in choices:
            offset = tuple((j + 1) % n for j, n in enumerate(moduli))
            psi = coset_quadratic_state(group, steps, offset)
            psi_q = group.profile(psi)
            true_h = {u for u, value in zip(group.phase_points, psi_q)
                      if value > 1 - TOL}
            assert len(true_h) == group.n
            assert np.max(np.minimum(abs(psi_q), abs(psi_q - 1))) < TOL
            assert all(abs(group.beta(a, b) - 1) < TOL for a in true_h for b in true_h)
            for t in [1e-5, 1e-4, 1e-3, 0.025, 0.1, 0.16]:
                z = rng.normal(size=group.n) + 1j * rng.normal(size=group.n)
                z = normalized(z - np.vdot(psi, z) * psi)
                state = math.sqrt(1 - t) * psi + math.sqrt(t) * z
                q = group.profile(state)
                kappa = float(np.sum(q * q) / group.n)
                delta = 1 - kappa
                violation = max(0.0, kappa - (1 - local_defect(t)))
                residuals["envelope_violation"] = max(
                    residuals["envelope_violation"], violation)
                assert violation < TOL
                row = {"moduli": list(moduli), "subgroup_steps": list(steps),
                       "coset_support_size": int(np.count_nonzero(abs(psi) > TOL)),
                       "t": t, "kappa": kappa, "delta": delta,
                       "envelope_slack": float(1 - local_defect(t) - kappa)}
                if delta < 1 / 120:
                    high = [u for u, value in zip(group.phase_points, q)
                            if value >= 19 / 20]
                    recovered = {group.phase_sub(a, b) for a in high for b in high}
                    assert len(recovered) == group.n and recovered == true_h
                    assert all(group.phase_add(a, b) in recovered
                               for a in recovered for b in recovered)
                    rho = group.twirl(state, recovered)
                    probabilities, eigenvectors = np.linalg.eigh(rho)
                    fidelity = float(probabilities[-1])
                    bound = 1 - inverse_defect(delta)
                    residuals["inverse_bound_violation"] = max(
                        residuals["inverse_bound_violation"], max(0.0, bound - fidelity))
                    assert fidelity >= 1 - 20 * delta - TOL
                    assert fidelity >= bound - TOL
                    row.update({"high_set_size": len(high),
                                "recovered_subgroup_size": len(recovered),
                                "recovered_state_fidelity": fidelity,
                                "sharp_fidelity_lower_bound": bound})
                summary["near_coset_examples"].append(row)

    # Exact saturating states in each tested near-regime, evaluated numerically.
    group = AbelianGroup((2,))
    summary["c2_numerical_saturation"] = []
    for t in [1e-6, 1e-5, 1e-4, 1e-3]:
        v = np.array([math.sqrt(1 - t), math.sqrt(t)], dtype=complex)
        q = group.profile(v)
        delta = 1 - float(np.sum(q * q) / 2)
        inverse_error = abs(inverse_defect(delta) - t)
        assert inverse_error < TOL
        summary["c2_numerical_saturation"].append(
            {"t": t, "delta": delta, "inverse_error": inverse_error})
    summary["maximum_observed_residuals"] = residuals
    summary["checks_passed"] = True
    summary["near_coset_example_count"] = len(summary["near_coset_examples"])
    return summary


if __name__ == "__main__":
    result = verify()
    output = Path(__file__).resolve().parents[1] / "data" / "spectral_rigidity_checks.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"checks_passed": result["checks_passed"],
                      "groups": len(result["groups"]),
                      "near_coset_examples": result["near_coset_example_count"],
                      "maximum_observed_residuals": result["maximum_observed_residuals"],
                      "output": str(output)}, indent=2))
