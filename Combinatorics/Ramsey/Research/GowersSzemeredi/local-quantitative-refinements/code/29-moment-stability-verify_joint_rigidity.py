#!/usr/bin/env python3
"""Finite, reproducible diagnostics for joint derivative-spectrum rigidity.

Exact checks use integers/Fraction for quadratic integration and exhaustive
homomorphism repair. Other checks use NumPy complex128 and are diagnostics,
not proofs of the universal theorem. No external data are required.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np


SEED = 20261006
TOL = 2e-10


class Group:
    def __init__(self, moduli):
        self.moduli = tuple(moduli)
        self.elements = list(itertools.product(*(range(n) for n in moduli)))
        self.index = {x: i for i, x in enumerate(self.elements)}
        self.n = len(self.elements)
        self.zero = self.index[tuple(0 for _ in moduli)]
        self.add = np.empty((self.n, self.n), dtype=int)
        self.sub = np.empty_like(self.add)
        for i, x in enumerate(self.elements):
            for j, y in enumerate(self.elements):
                self.add[i, j] = self.index[
                    tuple((a + b) % n for a, b, n in zip(x, y, moduli))
                ]
                self.sub[i, j] = self.index[
                    tuple((a - b) % n for a, b, n in zip(x, y, moduli))
                ]
        self.characters = np.array([
            [np.exp(2j * np.pi * sum(a * b / n for a, b, n in
                                    zip(r, x, moduli)))
             for x in self.elements]
            for r in self.elements
        ])
        self.bases = [self.index[tuple(int(i == j) for i in range(len(moduli)))]
                      for j in range(len(moduli))]

    def coefficients(self, f, g=None):
        if g is None:
            g = f
        derivative = f[None, :] * np.conj(g[self.sub.T])
        # self.sub[x,h] is x-h; row h needs the transpose.
        return derivative @ self.characters.conj().T / self.n

    def character_fraction(self, frequency, point):
        return sum((Fraction(a * b, n) for a, b, n in
                    zip(self.elements[frequency], self.elements[point],
                        self.moduli)), Fraction(0)) % 1


def normalized(f):
    return f / math.sqrt(float(np.mean(np.abs(f) ** 2)))


def random_normalized(group, rng):
    return normalized(rng.normal(size=group.n) + 1j * rng.normal(size=group.n))


def statistic(a, w):
    return float(np.mean(np.sum(w * np.abs(a) ** 2, axis=1)))


def graph_statistic(a, phi):
    return float(np.mean(np.abs(a[np.arange(len(phi)), phi]) ** 2))


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def close(x, y, message, tol=TOL):
    error = float(np.max(np.abs(np.asarray(x) - np.asarray(y))))
    require(error <= tol, f"{message}: absolute error {error:.6g}")
    return error


def integrate(group, theta, roots=None):
    """Integrate a symmetric bicharacter by exact rational phase arithmetic."""
    if roots is None:
        roots = [0] * len(group.moduli)
    phases = []
    psi = []
    for x in group.elements:
        phase = Fraction(0)
        for i, n in enumerate(group.moduli):
            u_phase = -theta[i][i] * Fraction(n - 1, 2) + Fraction(roots[i], n)
            phase += u_phase * x[i] + theta[i][i] * Fraction(x[i] * (x[i] - 1), 2)
        for i in range(len(x)):
            for j in range(i + 1, len(x)):
                phase += theta[i][j] * x[i] * x[j]
        phases.append(phase % 1)
        frequency = []
        for j, n in enumerate(group.moduli):
            coefficient = n * sum((theta[i][j] * x[i] for i in range(len(x))),
                                  Fraction(0))
            require(coefficient.denominator == 1, "Bicharacter integrality")
            frequency.append(int(coefficient) % n)
        psi.append(group.index[tuple(frequency)])
    q = np.exp(2j * np.pi * np.array([float(x) for x in phases]))
    return phases, np.asarray(psi), q


def random_quadratic(group, rng):
    r = len(group.moduli)
    theta = [[Fraction(0) for _ in range(r)] for _ in range(r)]
    for i in range(r):
        for j in range(i, r):
            order = math.gcd(group.moduli[i], group.moduli[j])
            theta[i][j] = theta[j][i] = Fraction(int(rng.integers(order)), order)
    roots = [int(rng.integers(n)) for n in group.moduli]
    phases, psi, q = integrate(group, theta, roots)
    return theta, phases, psi, q


def repair(group, phi):
    differences = group.sub[phi[group.add], phi[None, :]]
    psi = np.array([np.bincount(row, minlength=group.n).argmax()
                    for row in differences])
    require(np.all(psi[group.add] == group.add[psi[:, None], psi[None, :]]),
            "Majority output is not a homomorphism")
    return psi


def recover_self(group, f, w):
    a = group.coefficients(f)
    phi = np.argmax(np.abs(a) ** 2, axis=1)
    psi = repair(group, phi)
    theta = [[group.character_fraction(psi[e_i], e_j) for e_j in group.bases]
             for e_i in group.bases]
    require(theta == list(map(list, zip(*theta))), "Recovered symmetry")
    _, integrated_psi, q0 = integrate(group, theta)
    require(np.array_equal(psi, integrated_psi), "Recovered derivative map")
    g = f * q0.conj()
    fourier = group.characters.conj() @ g / group.n
    chi = int(np.argmax(np.abs(fourier)))
    c = fourier[chi] / abs(fourier[chi])
    q = q0 * group.characters[chi]
    function_error = float(np.mean(np.abs(f - c * q) ** 2))
    weight_error = float(np.mean(1 - w[np.arange(group.n), psi]))
    return dict(q=q, c=c, psi=psi, function_error=function_error,
                weight_error=weight_error)


def selector(group, correct, off_mass, missing_mass, rng):
    w = np.zeros((group.n, group.n))
    for h in range(group.n):
        bad = (int(correct[h]) + 1 + int(rng.integers(group.n - 1))) % group.n
        w[h, correct[h]] = 1 - off_mass - missing_mass
        w[h, bad] = off_mass
    return w


def exact_integration_checks(groups, rng):
    cases = pairs = derivatives = 0
    for group in groups:
        for _ in range(12):
            theta, phases, psi, q = random_quadratic(group, rng)
            for ix, x in enumerate(group.elements):
                for iy, y in enumerate(group.elements):
                    bxy = sum((theta[i][j] * x[i] * y[j]
                               for i in range(len(x)) for j in range(len(x))),
                              Fraction(0))
                    require((phases[group.add[ix, iy]] - phases[ix] - phases[iy]
                             - bxy) % 1 == 0, "Exact polarization")
                    pairs += 1
                    ch = phases[iy] - group.character_fraction(psi[iy], iy)
                    require((phases[ix] - phases[group.sub[ix, iy]] - ch
                             - group.character_fraction(psi[iy], ix)) % 1 == 0,
                            "Exact derivative integration")
                    derivatives += 1
            a = group.coefficients(q)
            close(graph_statistic(a, psi), 1, "Quadratic exact spectrum")
            cases += 1
    two = Group((2,))
    phases, _, _ = integrate(two, [[Fraction(1, 2)]])
    require(phases[1].denominator == 4, "Even-order nonclassical phase")
    return dict(cases=cases, exact_polarization_pairs=pairs,
                exact_derivative_pairs=derivatives,
                even_group_fourth_root_example=str(phases[1]))


def exhaustive_blr_checks():
    # All 2^16 maps F_2^4 -> F_2, including nonhomomorphic accepted maps.
    n = 16
    add = np.bitwise_xor.outer(np.arange(n), np.arange(n))
    accepted = nonhomomorphic = 0
    max_failure_numerator = 0
    max_mismatch = 0
    for start in range(0, 1 << n, 1024):
        labels = np.arange(start, min(start + 1024, 1 << n), dtype=np.uint32)
        maps = ((labels[:, None] >> np.arange(n)) & 1).astype(np.uint8)
        failure = maps[:, add] ^ maps[:, :, None] ^ maps[:, None, :]
        counts = failure.sum(axis=(1, 2))
        for phi, count_value in zip(maps[6 * counts < n * n],
                                    counts[6 * counts < n * n]):
            count = int(count_value)
            differences = phi[add] ^ phi[None, :]
            ones = differences.sum(axis=1)
            majority_mass = np.maximum(ones, n - ones)
            psi = (ones > n // 2).astype(np.uint8)
            require(np.all(majority_mass * n >= n * n - 2 * count),
                    "Exact majority mass")
            require(np.all(psi[add] == (psi[:, None] ^ psi[None, :])),
                    "Exact repaired homomorphism")
            mismatch = int(np.sum(phi != psi))
            require(mismatch * (n * n - 2 * count) <= n * count,
                    "Exact BLR mismatch bound")
            errors = (phi != psi).astype(np.uint8)
            error_count = errors[:, None] + errors[None, :] + errors[add]
            exactly_one = int(np.sum(error_count == 1))
            all_three = int(np.sum(error_count == 3))
            require(exactly_one == 3 * mismatch * n - 6 * mismatch ** 2
                    + 3 * all_three, "Exact one-error counting identity")
            require(count >= exactly_one, "A unique error forces test rejection")
            require(count >= 3 * mismatch * n - 6 * mismatch ** 2,
                    "Sharpened homomorphism-testing lower bound")
            accepted += 1
            nonhomomorphic += int(count != 0)
            max_failure_numerator = max(max_failure_numerator, count)
            max_mismatch = max(max_mismatch, mismatch)
    # An additional nonbinary target tests that no XOR-specific step is assumed.
    n, target = 4, 3
    add = (np.arange(n)[:, None] + np.arange(n)[None, :]) % n
    ternary_accepted = 0
    for values in itertools.product(range(target), repeat=n):
        phi = np.array(values)
        count = int(np.sum((phi[add] - phi[:, None] - phi[None, :]) % target != 0))
        if 6 * count >= n * n:
            continue
        differences = (phi[add] - phi[None, :]) % target
        psi = np.array([np.bincount(row, minlength=target).argmax()
                        for row in differences])
        require(np.all((psi[add] - psi[:, None] - psi[None, :]) % target == 0),
                "Ternary target homomorphism")
        mismatch = int(np.sum(phi != psi))
        require(mismatch * (n * n - 2 * count) <= n * count,
                "Ternary target exact mismatch")
        ternary_accepted += 1
    require(nonhomomorphic > 0, "Exhaustive test must cover actual repairs")
    return dict(binary_functions=1 << 16, binary_accepted=accepted,
                binary_nonhomomorphic_accepted=nonhomomorphic,
                binary_max_failure_fraction=f"{max_failure_numerator}/256",
                binary_max_repaired_mismatches=max_mismatch,
                ternary_functions=3 ** 4, ternary_accepted=ternary_accepted)


def exact_constant_checks():
    epsilon = Fraction(1, 512)
    crude = Fraction(54) / (1 - 108 * epsilon)
    first = Fraction(54) / (3 - 414 * epsilon)
    second = Fraction(54) / (3 - 150 * epsilon)
    require(crude < 69 and first < 25 and second < 20,
            "Exact two-step bootstrap constants")
    require(208 * epsilon < 1, "Exact symmetry threshold")
    require(1 - 21 * epsilon >= Fraction(100, 121),
            "Exact squared Fourier-distance constant")
    require(Fraction(6, 4096) < Fraction(1, 512),
            "Mixed-to-self permitted defect range")
    # (sqrt(2)+12)^2 = 146+24sqrt(2)<180 iff 2<(17/12)^2.
    require(Fraction(2) < Fraction(17, 12) ** 2,
            "Exact mixed second-function constant")
    return dict(crude_factor=str(crude), first_bootstrap_factor=str(first),
                second_bootstrap_factor=str(second),
                self_defect_range="0 <= epsilon <= 1/512",
                self_hamming_constant=20, self_function_constant=22,
                self_weight_constant=22, self_headline_constant=24,
                mixed_defect_range="0 <= epsilon <= 1/4096",
                mixed_headline_constant=192)


def averaged_symmetry_checks(groups, rng):
    cases = nonsymmetric = 0
    maximum_identity_error = 0.0
    minimum_bound_margin = float("inf")
    for group in groups:
        r = len(group.moduli)
        for _ in range(12):
            theta = [[Fraction(int(rng.integers(math.gcd(ni, nj))),
                               math.gcd(ni, nj))
                      for nj in group.moduli] for ni in group.moduli]
            psi = []
            for h in group.elements:
                frequency = []
                for j, n in enumerate(group.moduli):
                    value = n * sum((theta[i][j] * h[i] for i in range(r)),
                                    Fraction(0))
                    require(value.denominator == 1, "Random homomorphism integrality")
                    frequency.append(int(value) % n)
                psi.append(group.index[tuple(frequency)])
            psi = np.array(psi)
            b = group.characters[psi, :]
            q = np.exp(1j * rng.uniform(-np.pi, np.pi, size=group.n))
            derivative = q[None, :] * np.conj(q[group.sub.T])
            a = group.coefficients(q)
            zeta = 1 - graph_statistic(a, psi)
            row_errors = []
            for h in range(group.n):
                double_derivative = (derivative[h][None, :] *
                                     np.conj(derivative[h][group.sub.T]))
                observed = float(np.mean(np.abs(double_derivative - b[h, :, None]) ** 2))
                u_h = derivative[h] * group.characters[psi[h]].conj()
                predicted = 2 - 2 * abs(np.mean(u_h)) ** 2
                maximum_identity_error = max(maximum_identity_error,
                    close(observed, predicted, "Averaged double-derivative identity"))
                row_errors.append(observed)
            maximum_identity_error = max(maximum_identity_error,
                close(np.mean(row_errors), 2 * zeta, "Exact averaged symmetry energy"))
            defect = float(np.mean(np.abs(b - b.T) ** 2))
            require(defect <= 8 * zeta + TOL, "Improved eight-zeta symmetry inequality")
            if defect > TOL:
                require(defect >= 1 - TOL, "Nontrivial commutator orthogonality gap")
                nonsymmetric += 1
            minimum_bound_margin = min(minimum_bound_margin, 8 * zeta - defect)
            cases += 1
    require(nonsymmetric > 0, "Symmetry checks must include an actual obstruction")
    return dict(cases=cases, nonsymmetric_cases=nonsymmetric,
                maximum_identity_error=maximum_identity_error,
                minimum_eight_zeta_margin=minimum_bound_margin)


def mixed_identity_checks(groups, rng):
    cases = 0
    maximum_error = 0.0
    minimum_contraction_margin = float("inf")
    for group in groups:
        for _ in range(10):
            f, g = random_normalized(group, rng), random_normalized(group, rng)
            w = rng.random((group.n, group.n))
            w /= w.sum(axis=1, keepdims=True)
            w *= rng.random((group.n, 1))
            a = group.coefficients(f, g)
            maximum_error = max(maximum_error,
                close(np.mean(np.sum(np.abs(a) ** 2, axis=1)), 1,
                      "Mixed global Parseval"))
            h0, chi0 = np.unravel_index(np.argmax(np.abs(a)), a.shape)
            c = a[h0, chi0] / abs(a[h0, chi0])
            plus = group.add[:, h0]
            g0 = c.conjugate() * group.characters[chi0, plus].conj() * f[plus]
            a0 = group.coefficients(f, g0)
            af = group.coefficients(f)
            k = group.sub[:, h0]
            xi = group.sub[:, chi0]
            scalar = c * group.characters[chi0, group.sub[h0, :]]
            predicted = scalar[:, None] * af[k[:, None], xi[None, :]]
            maximum_error = max(maximum_error,
                close(a0, predicted, "Mixed shift/modulation identity"))
            w0 = w[group.add[:, h0][:, None], group.add[:, chi0][None, :]]
            maximum_error = max(maximum_error,
                close(statistic(a0, w), statistic(af, w0), "Mixed weight transform"))
            d0 = float(np.mean(np.abs(g - g0) ** 2))
            maximum_error = max(maximum_error,
                close(np.mean(np.sum(np.abs(a - a0) ** 2, axis=1)), d0,
                      "Mixed tensor distance"))
            bound = (math.sqrt(max(0, 1 - statistic(a, w))) + math.sqrt(d0)) ** 2
            margin = bound - (1 - statistic(a0, w))
            require(margin >= -TOL, "Complementary weight contraction")
            minimum_contraction_margin = min(minimum_contraction_margin, margin)
            cases += 1
    return dict(cases=cases, maximum_identity_error=maximum_error,
                minimum_contraction_margin=minimum_contraction_margin)


def endpoint_checks(groups, rng):
    self_cases = mixed_cases = 0
    max_self_ratio = max_self_weight_ratio = 0.0
    max_mixed_function_ratio = max_mixed_weight_ratio = 0.0
    for group in groups:
        for scale in (1e-5, 3e-5, 1e-4, 3e-4):
            _, _, psi, q = random_quadratic(group, rng)
            f = normalized(q * (1 + scale * rng.normal(size=group.n)) *
                           np.exp(1j * scale * rng.normal(size=group.n)))
            w = selector(group, psi, scale ** 2, scale ** 2 / 2, rng)
            epsilon = 1 - statistic(group.coefficients(f), w)
            require(0 < epsilon <= 2 ** -9, "Self synthetic defect regime")
            recovered = recover_self(group, f, w)
            require(recovered["function_error"] <= 24 * epsilon + TOL,
                    "Self reconstruction function bound")
            require(recovered["weight_error"] <= 24 * epsilon + TOL,
                    "Self reconstruction selector bound")
            max_self_ratio = max(max_self_ratio, recovered["function_error"] / epsilon)
            max_self_weight_ratio = max(max_self_weight_ratio,
                                       recovered["weight_error"] / epsilon)
            self_cases += 1

            rho = int(rng.integers(group.n))
            g = normalized(q * group.characters[rho].conj() *
                           (1 + scale * rng.normal(size=group.n)) *
                           np.exp(1j * scale * rng.normal(size=group.n)))
            correct = group.add[psi, rho]
            wm = selector(group, correct, scale ** 2, scale ** 2 / 2, rng)
            a = group.coefficients(f, g)
            epsilon = 1 - statistic(a, wm)
            require(0 < epsilon <= 2 ** -12, "Mixed synthetic defect regime")
            h0, chi0 = np.unravel_index(np.argmax(np.abs(a)), a.shape)
            c0 = a[h0, chi0] / abs(a[h0, chi0])
            plus = group.add[:, h0]
            g0 = c0.conjugate() * group.characters[chi0, plus].conj() * f[plus]
            w0 = wm[group.add[:, h0][:, None], group.add[:, chi0][None, :]]
            epsilon0 = 1 - statistic(group.coefficients(f), w0)
            require(epsilon0 <= 6 * epsilon + TOL, "Mixed-to-self defect")
            recovered = recover_self(group, f, w0)
            f_model = recovered["c"] * recovered["q"]
            g_model = c0.conjugate() * group.characters[chi0, plus].conj() * f_model[plus]
            recovered_rho = group.sub[chi0, recovered["psi"][h0]]
            affine = group.add[recovered["psi"], recovered_rho]
            f_error = float(np.mean(np.abs(f - f_model) ** 2))
            g_error = float(np.mean(np.abs(g - g_model) ** 2))
            weight_error = float(np.mean(1 - wm[np.arange(group.n), affine]))
            ratio = g_model / (recovered["q"] * group.characters[recovered_rho].conj())
            close(ratio, ratio[0], "Recovered relative character")
            require(max(f_error, g_error, weight_error) <= 192 * epsilon + TOL,
                    "Mixed reconstruction theorem")
            max_mixed_function_ratio = max(max_mixed_function_ratio,
                                           f_error / epsilon, g_error / epsilon)
            max_mixed_weight_ratio = max(max_mixed_weight_ratio, weight_error / epsilon)
            mixed_cases += 1
    return dict(self_cases=self_cases, mixed_cases=mixed_cases,
                max_self_function_error_over_defect=max_self_ratio,
                max_self_weight_error_over_defect=max_self_weight_ratio,
                max_mixed_function_error_over_defect=max_mixed_function_ratio,
                max_mixed_weight_error_over_defect=max_mixed_weight_ratio)


def selector_at_target(group, a, correct, target, rng):
    bad = (correct + 1 + rng.integers(group.n - 1, size=group.n)) % group.n
    good_energy = graph_statistic(a, correct)
    bad_energy = graph_statistic(a, bad)
    mass = (good_energy - 1 + target) / (good_energy - bad_energy / 2)
    require(0 <= mass <= 1, "Target selector feasibility")
    w = np.zeros((group.n, group.n))
    w[np.arange(group.n), correct] = 1 - mass
    w[np.arange(group.n), bad] = mass / 2
    close(1 - statistic(a, w), target, "Prescribed near-threshold defect")
    return w


def near_threshold_checks(groups, rng):
    self_cases = mixed_cases = 0
    maximum_self_defect = maximum_mixed_defect = 0.0
    maximum_function_ratio = maximum_selector_ratio = 0.0
    for group in groups:
        for fraction in (0.25, 0.9, 0.999):
            _, _, psi, q = random_quadratic(group, rng)
            scale = 2e-4
            f = normalized(q * (1 + scale * rng.normal(size=group.n)) *
                           np.exp(1j * scale * rng.normal(size=group.n)))
            a = group.coefficients(f)
            target = fraction / 512
            w = selector_at_target(group, a, psi, target, rng)
            rec = recover_self(group, f, w)
            require(rec["function_error"] <= 22 * target + TOL,
                    "Near-threshold self function error")
            require(rec["weight_error"] <= 22 * target + TOL,
                    "Near-threshold self selector error")
            maximum_self_defect = max(maximum_self_defect, target)
            maximum_function_ratio = max(maximum_function_ratio,
                                         rec["function_error"] / target)
            maximum_selector_ratio = max(maximum_selector_ratio,
                                         rec["weight_error"] / target)
            self_cases += 1

            rho = int(rng.integers(group.n))
            g = normalized(q * group.characters[rho].conj() *
                           (1 + scale * rng.normal(size=group.n)) *
                           np.exp(1j * scale * rng.normal(size=group.n)))
            a = group.coefficients(f, g)
            correct = group.add[psi, rho]
            target = fraction / 4096
            w = selector_at_target(group, a, correct, target, rng)
            h0, chi0 = np.unravel_index(np.argmax(np.abs(a)), a.shape)
            c0 = a[h0, chi0] / abs(a[h0, chi0])
            plus = group.add[:, h0]
            w0 = w[group.add[:, h0][:, None], group.add[:, chi0][None, :]]
            epsilon0 = 1 - statistic(group.coefficients(f), w0)
            require(epsilon0 <= 6 * target + TOL,
                    "Near-threshold mixed-to-self defect")
            rec = recover_self(group, f, w0)
            f_model = rec["c"] * rec["q"]
            g_model = c0.conjugate() * group.characters[chi0, plus].conj() * f_model[plus]
            recovered_rho = group.sub[chi0, rec["psi"][h0]]
            affine = group.add[rec["psi"], recovered_rho]
            f_error = float(np.mean(np.abs(f - f_model) ** 2))
            g_error = float(np.mean(np.abs(g - g_model) ** 2))
            w_error = float(np.mean(1 - w[np.arange(group.n), affine]))
            require(max(f_error, g_error, w_error) <= 192 * target + TOL,
                    "Near-threshold mixed reconstruction")
            maximum_mixed_defect = max(maximum_mixed_defect, target)
            maximum_function_ratio = max(maximum_function_ratio,
                                         f_error / target, g_error / target)
            maximum_selector_ratio = max(maximum_selector_ratio, w_error / target)
            mixed_cases += 1
    return dict(self_cases=self_cases, mixed_cases=mixed_cases,
                maximum_self_defect=maximum_self_defect,
                maximum_mixed_defect=maximum_mixed_defect,
                fraction_of_allowed_endpoint_tested=0.999,
                maximum_function_error_over_defect=maximum_function_ratio,
                maximum_selector_error_over_defect=maximum_selector_ratio)


def sharp_rate_checks():
    group = Group((2,))
    chi = group.characters[1].real
    rows = []
    for t in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7):
        f = math.sqrt(1 - t) + math.sqrt(t) * chi
        a = group.coefficients(f)
        epsilon = 2 * t * (1 - t)
        exact_error = 2 * t / (1 + math.sqrt(1 - t))
        close(1 - graph_statistic(a, np.zeros(2, dtype=int)), epsilon,
              "Sharp-rate correlation polynomial")
        close(np.mean(np.abs(f - 1) ** 2), exact_error,
              "Sharp-rate amplitude distance")
        rows.append(dict(t=t, defect=epsilon, squared_distance=exact_error,
                         distance_over_defect=exact_error / epsilon))
        w = np.array([[1 - epsilon, epsilon], [1 - epsilon, epsilon]])
        close(statistic(group.coefficients(np.ones(2)), w), 1 - epsilon,
              "Sharp selector statistic")
        close(np.mean(1 - w[:, 0]), epsilon, "Sharp selector mass defect")
    require(abs(rows[-1]["distance_over_defect"] - 0.5) < 1e-6,
            "Sharp-rate limiting constant")
    return dict(cases=len(rows), rows=rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rng = np.random.default_rng(SEED)
    groups = [Group(m) for m in ((2,), (4,), (8,), (2, 2), (2, 4),
                                (3, 4), (2, 2, 2), (2, 3, 4))]
    result = dict(seed=SEED, numpy_version=np.__version__, tolerance=TOL,
                  groups=[list(g.moduli) for g in groups],
                  exact_constants=exact_constant_checks(),
                  exact_integration=exact_integration_checks(groups, rng),
                  exact_exhaustive_blr=exhaustive_blr_checks(),
                  averaged_symmetry=averaged_symmetry_checks(groups, rng),
                  mixed_identities=mixed_identity_checks(groups, rng),
                  endpoint_reconstruction=endpoint_checks(groups, rng),
                  near_threshold_reconstruction=near_threshold_checks(groups, rng),
                  sharp_rate=sharp_rate_checks(),
                  status="PASS",
                  scope="Exact finite checks and complex128 diagnostics; universal proofs are in the article.")
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
