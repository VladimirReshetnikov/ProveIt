#!/usr/bin/env python3
"""Dependency-free sparse integer-polynomial compiler for RLE rotor networks.

The output is an expanded quartic, not a call to a Diophantine existence oracle.
Natural-number witness semantics are essential. Python 3.10+ is required.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from verify_certificates import Network, rle_witness, rle_residuals

Monomial = tuple[tuple[str, int], ...]


@dataclass
class Poly:
    terms: dict[Monomial, int]

    @staticmethod
    def constant(value: int) -> Poly:
        return Poly({(): value} if value else {})

    @staticmethod
    def variable(name: str) -> Poly:
        return Poly({((name, 1),): 1})

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        return value if isinstance(value, Poly) else Poly.constant(value)

    def __add__(self, other: Poly | int) -> Poly:
        terms = self.terms.copy()
        for monomial, coefficient in self.coerce(other).terms.items():
            terms[monomial] = terms.get(monomial, 0) + coefficient
            if not terms[monomial]:
                del terms[monomial]
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({monomial: -coefficient for monomial, coefficient in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) - self

    def __mul__(self, other: Poly | int) -> Poly:
        terms: dict[Monomial, int] = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in self.coerce(other).terms.items():
                powers = dict(m1)
                for name, exponent in m2:
                    powers[name] = powers.get(name, 0) + exponent
                monomial = tuple(sorted(powers.items()))
                terms[monomial] = terms.get(monomial, 0) + c1 * c2
        return Poly({m: c for m, c in terms.items() if c})

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max((sum(exponent for _, exponent in m) for m in self.terms), default=0)

    def evaluate(self, assignment: dict[str, int]) -> int:
        value = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for name, exponent in monomial:
                term *= assignment[name] ** exponent
            value += term
        return value

    def serializable(self) -> list[dict]:
        return [{"coefficient": coefficient, "powers": dict(monomial)}
                for monomial, coefficient in sorted(self.terms.items())]

    def text(self) -> str:
        pieces = []
        for monomial, coefficient in sorted(self.terms.items()):
            factors = [name if exponent == 1 else f"{name}^{exponent}"
                       for name, exponent in monomial]
            pieces.append(str(coefficient) + ("*" + "*".join(factors) if factors else ""))
        return " + ".join(pieces).replace("+ -", "- ") or "0"


def compile_rle(net: Network, variable_lengths: bool = False
                ) -> tuple[list[str], list[str], list[Poly], Poly]:
    inputs = [f"x:{v}" for v in range(net.n)]
    if variable_lengths:
        inputs += [f"lambda:{v}:{j}" for v, blocks in enumerate(net.periods)
                   for j in range(len(blocks))]
    names = [f"{name}:{v}" for v in range(net.n) for name in ("u", "q", "z", "h")]
    names += [f"{name}:{v}:{j}" for v, blocks in enumerate(net.periods)
              for j in range(len(blocks)) for name in ("b", "t", "alpha", "beta")]
    names += [f"y:{s}" for s in range(net.sinks)]
    var = {name: Poly.variable(name) for name in inputs + names}
    zero = Poly.constant(0)
    flow = [[zero for _ in range(net.n + net.sinks)] for _ in range(net.n)]
    residuals: list[Poly] = []
    for v, blocks in enumerate(net.periods):
        q, z, u, h = (var[f"{name}:{v}"] for name in ("q", "z", "u", "h"))
        previous: list[Poly | int] = [0] * (net.n + net.sinks)
        selection = phase = height_sum = zero
        period_length = zero
        for j, (dest, fixed_length) in enumerate(blocks):
            length = var[f"lambda:{v}:{j}"] + 1 if variable_lengths else fixed_length
            period_length += length
            b, t, alpha, beta = (var[f"{name}:{v}:{j}"]
                                 for name in ("b", "t", "alpha", "beta"))
            selection += b
            phase += sum(previous) * b + t
            for target in range(net.n + net.sinks):
                flow[v][target] += previous[target] * b
            flow[v][dest] += t + length * q
            if dest < net.n:
                height_sum += b * var[f"h:{dest}"]
            residuals += [t - b - alpha, t + beta - length * b]
            previous[dest] += length
        residuals += [z * (z - 1), selection - z, q * (1 - z),
                      u - period_length * q - phase, h - z - height_sum]
    residuals += [var[f"u:{v}"] - var[f"x:{v}"]
                  - sum((flow[a][v] for a in range(net.n)), zero)
                  for v in range(net.n)]
    residuals += [var[f"y:{s}"]
                  - sum((flow[v][net.n + s] for v in range(net.n)), zero)
                  for s in range(net.sinks)]
    quartic = sum((r * r for r in residuals), zero)
    assert len(names) == 4 * net.n + 4 * net.m + net.sinks
    assert len(residuals) == 6 * net.n + 2 * net.m + net.sinks
    assert all(r.degree <= 2 for r in residuals) and quartic.degree <= 4
    return inputs, names, residuals, quartic


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("example_quartic.json"))
    parser.add_argument("--variable-lengths", action="store_true")
    args = parser.parse_args()
    net = Network((((0, 3), (1, 1)),), 1)
    inputs, names, residuals, quartic = compile_rle(net, args.variable_lengths)
    witness = rle_witness(net, (8,))
    assert witness is not None
    assignment = {**witness, "x:0": 2}
    if args.variable_lengths:
        assignment.update({"lambda:0:0": 2, "lambda:0:1": 0})
    assert [r.evaluate(assignment) for r in residuals] == rle_residuals(net, (2,), witness)
    assert quartic.evaluate(assignment) == 0
    mutation_checks = 0
    # Symbolic-versus-direct evaluator crosschecks at arbitrary, not just valid, points.
    import random
    rng = random.Random(20260930)
    for _ in range(500):
        sample = {name: rng.randrange(10) for name in inputs + names}
        sample_net = (Network((((0, sample["lambda:0:0"] + 1),
                                (1, sample["lambda:0:1"] + 1)),), 1)
                      if args.variable_lengths else net)
        direct = rle_residuals(sample_net, (sample["x:0"],),
                               {name: sample[name] for name in names})
        assert [r.evaluate(sample) for r in residuals] == direct
        assert quartic.evaluate(sample) == sum(r * r for r in direct)
    for name in names:
        bad = assignment.copy()
        bad[name] += 1
        assert quartic.evaluate(bad) > 0
        mutation_checks += 1
    payload = {
        "model": ("one active vertex; period self^(lambda:0:0+1) sink^(lambda:0:1+1)"
                  if args.variable_lengths else "one active vertex; period self^3 sink"),
        "coefficient_domain": "integers", "witness_domain": "nonnegative integers",
        "input_variables": inputs, "witness_variables": names,
        "residual_count": len(residuals), "degree": quartic.degree,
        "expanded_monomials": len(quartic.terms),
        "residuals": [r.serializable() for r in residuals],
        "quartic": quartic.serializable(), "sample_root": assignment,
        "sample_root_evaluation": quartic.evaluate(assignment),
        "arbitrary_assignment_crosschecks": 500,
        "single_coordinate_mutations_rejected": mutation_checks}
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    args.output.with_suffix(".txt").write_text(
        "Q = sum of the squares of the following residuals:\n\n" +
        "\n".join(f"R{i+1} = {r.text()}" for i, r in enumerate(residuals)) +
        "\n\nExpanded Q:\n" + quartic.text() + "\n", encoding="utf-8")
    print(json.dumps({k: payload[k] for k in ("residual_count", "degree", "expanded_monomials",
                      "arbitrary_assignment_crosschecks", "single_coordinate_mutations_rejected")}))


if __name__ == "__main__":
    main()
