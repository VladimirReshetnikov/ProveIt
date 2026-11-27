#!/usr/bin/env python3
"""Exact synthetic checks for the real-positive prime-weight theorem.

This program checks the reflection identities and the terminating Pell
reconstruction on explicit synthetic spectra.  It performs no numerical
RH or GRH verification, computes no Dirichlet zeros, and is not a proof
assistant certificate.  All arithmetic takes place in Q(sqrt(2)) using
fractions; there are no floating-point equality decisions.

Run: python3 real_weight_checks.py [--output verification.json]
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path


@dataclass(frozen=True)
class Qsqrt2:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    def __add__(self, other: Qsqrt2) -> Qsqrt2:
        return Qsqrt2(self.a + other.a, self.b + other.b)

    def __neg__(self) -> Qsqrt2:
        return Qsqrt2(-self.a, -self.b)

    def __sub__(self, other: Qsqrt2) -> Qsqrt2:
        return self + (-other)

    def scale(self, c: int | F) -> Qsqrt2:
        return Qsqrt2(c * self.a, c * self.b)

    def serial(self) -> dict[str, str]:
        return {"rational": str(self.a), "sqrt2_coefficient": str(self.b)}


ZERO = Qsqrt2()
ONE = Qsqrt2(1)
SQRT2 = Qsqrt2(0, 1)


def pell(k: int) -> tuple[int, int]:
    """Return p,q with (1+sqrt(2))**k = p+q*sqrt(2)."""
    p, q = 1, 0
    for _ in range(k):
        p, q = p + 2 * q, p + q
    assert p * p - 2 * q * q == (-1) ** k
    return p, q


def pell_shift(k: int) -> Qsqrt2:
    p, q = pell(k)
    return Qsqrt2(-2 * p, 2 * q)


class Spectrum:
    def __init__(self, atoms: dict[Qsqrt2, int]):
        assert all(isinstance(m, int) and m > 0 for m in atoms.values())
        self.atoms = dict(atoms)

    def m(self, x: Qsqrt2) -> int:
        return self.atoms.get(x, 0)

    def S(self, a: Qsqrt2, x: Qsqrt2) -> int:
        return self.m(a + x) + self.m(a - x)

    def delta(self, a: Qsqrt2, y: Qsqrt2) -> int:
        value = self.S(a, y + a) - self.S(ZERO, y)
        assert value == self.m(y + a.scale(2)) - self.m(y)
        return value

    def telescope(self, t: Qsqrt2, k: int) -> tuple[int, int]:
        p, q = pell(k)
        value = sum(self.delta(SQRT2, t + SQRT2.scale(2 * r))
                    for r in range(q))
        value -= sum(self.delta(ONE, t + SQRT2.scale(2 * q)
                                - ONE.scale(2 * s))
                     for s in range(1, p + 1))
        assert value == self.m(t + pell_shift(k)) - self.m(t)
        return value, p + q

    def reconstruct(self, t: Qsqrt2, max_k: int = 12) -> dict:
        rejected = []
        for k in range(1, max_k + 1):
            endpoint = t + pell_shift(k)
            endpoint_sum = self.S(ZERO, endpoint)
            if endpoint_sum:
                rejected.append({"k": k, "S0_at_endpoint": endpoint_sum})
                continue
            total, steps = self.telescope(t, k)
            recovered = -total
            assert recovered == self.m(t)
            assert self.m(endpoint) == 0
            return {"target": t.serial(), "expected": self.m(t),
                    "recovered": recovered, "first_successful_k": k,
                    "transport_steps": steps, "rejected_endpoints": rejected}
        raise AssertionError("Synthetic fixture exceeded its intended finite search")


def lattice_m(x: Qsqrt2, sign: int) -> int:
    """Mass of sum_k delta_(sign/3+2k), sign=+1 or -1."""
    if x.b:
        return 0
    quotient = (x.a - F(sign, 3)) / 2
    return int(quotient.denominator == 1)


def lattice_S(a: Qsqrt2, x: Qsqrt2, sign: int) -> int:
    return lattice_m(a + x, sign) + lattice_m(a - x, sign)


def run_checks() -> dict:
    anchor = Qsqrt2(F(3, 2))
    atoms = {
        ZERO: 4, anchor: 2, -anchor: 1,
        Qsqrt2(0, 2): 3,
        Qsqrt2(-1, 1): 5,
        Qsqrt2(1, -1): 2,
        Qsqrt2(F(7, 3), F(-2, 5)): 7,
    }
    # Make the first three Pell endpoints occupied at the anchor.
    # This forces genuine retries instead of a vacuous k=1 stop everywhere.
    for k, multiplicity in [(1, 2), (2, 1), (3, 3)]:
        atoms[anchor + pell_shift(k)] = multiplicity
    spectrum = Spectrum(atoms)
    targets = list(atoms) + [Qsqrt2(F(7, 5)), Qsqrt2(2, 1), Qsqrt2(-8, 3)]

    identity_checks = 0
    for target in targets:
        for k in range(1, 6):
            spectrum.telescope(target, k)
            identity_checks += 1
    reconstructions = [spectrum.reconstruct(t) for t in targets]
    anchor_result = next(r for r in reconstructions if r["target"] == anchor.serial())
    assert anchor_result["first_successful_k"] >= 4
    assert any(r["expected"] == 0 and r["recovered"] == 0 for r in reconstructions)
    assert any(r["expected"] > 1 for r in reconstructions)

    # Two distinct infinite spectra with exactly equal symmetrizations
    # about 0 and 1: reflection interchanges the two 2-periodic lattices.
    lattice_queries = [Qsqrt2(F(j, 3)) for j in range(-80, 81)]
    lattice_queries += [Qsqrt2(F(j, 2), 1) for j in range(-10, 11)]
    lattice_checks = 0
    for x in lattice_queries:
        assert lattice_m(-x, 1) == lattice_m(x, -1)
        assert lattice_m(x + ONE.scale(2), 1) == lattice_m(x, 1)
        for center in (ZERO, ONE):
            assert lattice_S(center, x, 1) == lattice_S(center, x, -1)
            lattice_checks += 1
    assert lattice_m(Qsqrt2(F(1, 3)), 1) == 1
    assert lattice_m(Qsqrt2(F(1, 3)), -1) == 0
    # The third irrational center distinguishes this counterexample.
    witness = Qsqrt2(F(1, 3)) - SQRT2
    assert lattice_S(SQRT2, witness, 1) != lattice_S(SQRT2, witness, -1)

    return {
        "status": "PASS",
        "arithmetic": "Exact rational pairs a+b*sqrt(2); no floating point",
        "scope": "Synthetic reflection/tomography checks only; not RH/GRH verification",
        "finite_spectrum_distinct_atoms": len(atoms),
        "finite_spectrum_total_multiplicity": sum(atoms.values()),
        "pell_telescope_identity_checks": identity_checks,
        "two_center_lattice_query_checks": lattice_checks,
        "two_center_counterexample": {
            "mu": "sum over k in Z of delta_(1/3+2k)",
            "nu": "sum over k in Z of delta_(-1/3+2k)",
            "equal_centers": ["0", "1"],
            "irrational_center_distinguishes": True,
        },
        "reconstructions": reconstructions,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks()
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
