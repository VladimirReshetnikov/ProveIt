#!/usr/bin/env python3
"""Compile fixed iterates of F_p(x)=sum(x**(p**j), j>=0) modulo p**q.

The output is an exact finite Cartier representation, not an automaton guessed
from a finite coefficient prefix.  Each query reads the index in base p, least
significant digit first.  Setup can be large: explicit dimension, sparse-term,
and work guards deliberately reject impractical instances.

Examples (Python 3.10+, standard library only):
    python cartier.py -p 2 -q 3 -m 2 -n 123456789
    python cartier.py -p 2 -q 2 -m 3 -n 100 --export matrices.json
    python cartier.py --verify --verification-output verification.json

Here m is FIXED during compilation.  This does not compile the diagonal whose
iteration depth itself equals the queried index.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from itertools import combinations_with_replacement
from math import comb, factorial, isqrt, prod
from pathlib import Path


class ResourceLimit(ValueError):
    """The exact construction would exceed a declared setup budget."""


@dataclass
class Budget:
    max_dimension: int = 1000
    max_terms: int = 200_000
    max_work: int = 10_000_000
    max_radix: int = 257
    work: int = 0

    def dimension(self, value: int) -> None:
        if value > self.max_dimension:
            raise ResourceLimit(
                f"Required module dimension {value} exceeds "
                f"--max-dimension {self.max_dimension}."
            )

    def terms(self, value: int) -> None:
        if value > self.max_terms:
            raise ResourceLimit(
                f"Sparse term count {value} exceeds --max-terms {self.max_terms}."
            )

    def tick(self, value: int = 1) -> None:
        self.work += value
        if self.work > self.max_work:
            raise ResourceLimit(f"Setup exceeded --max-work {self.max_work}.")


def add_term(row: dict, key, value: int, modulus: int) -> None:
    value = (row.get(key, 0) + value) % modulus
    if value:
        row[key] = value
    else:
        row.pop(key, None)


@dataclass(frozen=True)
class Module:
    p: int
    modulus: int
    # matrices[digit][source_generator][destination_generator]
    matrices: tuple
    initial: tuple[int, ...]
    output: tuple[int, ...]

    @property
    def dimension(self) -> int:
        return len(self.output)

    def transition(self, state, digit: int) -> tuple[int, ...]:
        result = [0] * self.dimension
        for i, value in enumerate(state):
            if value:
                for j, coefficient in self.matrices[digit][i].items():
                    result[j] = (result[j] + value * coefficient) % self.modulus
        return tuple(result)

    def coefficient(self, n: int) -> int:
        if n < 0:
            raise ValueError("The coefficient index must be nonnegative.")
        state = self.initial
        while n:
            n, digit = divmod(n, self.p)
            state = self.transition(state, digit)
        return sum(a * b for a, b in zip(state, self.output)) % self.modulus

    def statistics(self) -> dict:
        return {
            "dimension": self.dimension,
            "nonzero_transition_entries": sum(
                len(row) for matrix in self.matrices for row in matrix
            ),
        }

    def export(self) -> dict:
        return {
            "format": "cartier-module-v1",
            "prime": self.p,
            "modulus": self.modulus,
            "digit_order": "least significant first",
            "initial": self.initial,
            "output": self.output,
            "matrices": [
                [sorted(row.items()) for row in matrix]
                for matrix in self.matrices
            ],
            **self.statistics(),
        }


def make_module(p, modulus, matrices, initial, output, budget: Budget) -> Module:
    budget.dimension(len(output))
    result = Module(p, modulus, tuple(tuple(m) for m in matrices),
                    tuple(initial), tuple(output))
    budget.terms(result.statistics()["nonzero_transition_entries"])
    # Constant coefficients are unchanged by Lambda_0.  This identity also
    # guarantees that additional most-significant zero digits are harmless.
    for row, value in zip(result.matrices[0], result.output):
        assert sum(c * result.output[j] for j, c in row.items()) % modulus == value
    return result


def base_module(p: int, modulus: int, budget: Budget, identity=False) -> Module:
    # Generators are (1,F_p), or (1,x) when identity=True.
    matrices = [[{}, {}] for _ in range(p)]
    matrices[0][0] = {0: 1}
    if not identity:
        matrices[0][1] = {1: 1}
    matrices[1][1] = {0: 1}
    return make_module(p, modulus, matrices, (0, 1), (1, 0), budget)


def module_sum(modules: list[Module], budget: Budget) -> Module:
    if len(modules) == 1:
        return modules[0]
    p, modulus = modules[0].p, modules[0].modulus
    dimension = sum(m.dimension for m in modules)
    budget.dimension(dimension)
    matrices = [[{} for _ in range(dimension)] for _ in range(p)]
    initial, output, offset = [], [], 0
    for module in modules:
        assert (module.p, module.modulus) == (p, modulus)
        for digit in range(p):
            for i, row in enumerate(module.matrices[digit]):
                matrices[digit][offset + i] = {
                    offset + j: c for j, c in row.items()
                }
                budget.tick(len(row))
        initial.extend(module.initial)
        output.extend(module.output)
        offset += module.dimension
    return make_module(p, modulus, matrices, initial, output, budget)


def module_S(module: Module, budget: Budget) -> Module:
    """Adjoin C=S(B): Lambda_r C=Lambda_r B+[r=0] C."""
    if module.coefficient(0):
        raise ValueError("S(B) requires B(0)=0.")
    d, p, modulus = module.dimension, module.p, module.modulus
    budget.dimension(d + 1)
    matrices = []
    for digit in range(p):
        matrix = [dict(row) for row in module.matrices[digit]]
        row = {i: c for i, c in enumerate(
            module.transition(module.initial, digit)) if c}
        if digit == 0:
            row[d] = 1
        matrix.append(row)
        matrices.append(matrix)
    return make_module(p, modulus, matrices, [0] * d + [1],
                       list(module.output) + [0], budget)


def module_power(module: Module, k: int, budget: Budget) -> Module:
    """Use x**c * u**alpha, 0<=c<k and |alpha|=k, as generators."""
    if k == 1:
        return module
    if k < 1:
        raise ValueError("This constructor requires a positive power.")
    d, p, modulus = module.dimension, module.p, module.modulus
    count = comb(d + k - 1, k)
    dimension = k * count
    budget.dimension(dimension)
    monomials = list(combinations_with_replacement(range(d), k))
    locations = {monomial: i for i, monomial in enumerate(monomials)}
    matrices = [[{} for _ in range(dimension)] for _ in range(p)]
    parts = [
        [(digit, j, c) for digit in range(p)
         for j, c in module.matrices[digit][i].items()]
        for i in range(d)
    ]
    initial, output = [0] * dimension, [0] * dimension
    total_terms = 0
    for index, monomial in enumerate(monomials):
        multiplicities = Counter(monomial)
        multinomial = factorial(k) // prod(
            factorial(a) for a in multiplicities.values())
        initial[index] = (multinomial * prod(
            module.initial[i] for i in monomial)) % modulus
        output[index] = prod(module.output[i] for i in monomial) % modulus

        # z records the sum of input digits; the tuple records the symmetric
        # monomial in generators evaluated at x**p.
        expansion = {(0, ()): 1}
        for i in monomial:
            budget.tick(len(expansion) * len(parts[i]))
            next_expansion = {}
            for (degree, indices), a in expansion.items():
                for digit, j, b in parts[i]:
                    key = (degree + digit, tuple(sorted(indices + (j,))))
                    add_term(next_expansion, key, a * b, modulus)
            budget.terms(len(next_expansion))
            expansion = next_expansion
        budget.tick(k * len(expansion))
        for carry in range(k):
            source = carry * count + index
            for (degree, indices), value in expansion.items():
                next_carry, digit = divmod(degree + carry, p)
                assert next_carry < k
                destination = next_carry * count + locations[indices]
                add_term(matrices[digit][source], destination, value, modulus)
        total_terms += sum(
            len(matrices[digit][carry * count + index])
            for digit in range(p) for carry in range(k)
        )
        budget.terms(total_terms)
    return make_module(p, modulus, matrices, initial, output, budget)


def fixed_iterate(p: int, q: int, m: int, budget: Budget | None = None) -> Module:
    budget = budget or Budget()
    if p < 2 or p > budget.max_radix:
        raise ResourceLimit(f"Require 2 <= p <= --max-radix {budget.max_radix}.")
    if any(p % i == 0 for i in range(2, isqrt(p) + 1)):
        raise ValueError("p must be prime.")
    if q < 1 or m < 0:
        raise ValueError("Require q >= 1 and m >= 0.")
    if q * p.bit_length() > 4096:
        raise ResourceLimit(
            "q * bit_length(p) exceeds the conservative 4096-bit setup guard."
        )
    modulus = p ** q
    module = base_module(p, modulus, budget, identity=(m == 0))
    for _ in range(1, m):
        # Check the complete next dimension before compiling any of its powers.
        powers, k, next_dimension = [], 1, 1
        for j in range(q):
            rank = k * comb(module.dimension + k - 1, k)
            next_dimension += rank
            budget.dimension(next_dimension)
            powers.append(k)
            k *= p
        blocks = [module_power(module, k, budget) for k in powers]
        blocks[-1] = module_S(blocks[-1], budget)
        module = module_sum(blocks, budget)
    return module


def direct_coefficients(p: int, q: int, m: int, degree: int) -> list[int]:
    """Independent truncated Cauchy multiplication; no Cartier identities."""
    modulus = p ** q

    def multiply(a, b):
        result = [0] * (degree + 1)
        aa = [(i, c) for i, c in enumerate(a) if c]
        bb = [(i, c) for i, c in enumerate(b) if c]
        for i, c in aa:
            for j, d in bb:
                if i + j > degree:
                    break
                result[i + j] = (result[i + j] + c * d) % modulus
        return result

    series = [0] * (degree + 1)
    if degree:
        series[1] = 1
    for _ in range(m):
        result, power, k = [0] * (degree + 1), series, 1
        while k <= degree:
            result = [(a + b) % modulus for a, b in zip(result, power)]
            if k * p > degree:
                break
            old_power = power
            for _ in range(p - 1):
                power = multiply(power, old_power)
            k *= p
        series = result
    return series


def verify() -> dict:
    cases = [(2, 2, 2), (2, 3, 2), (3, 2, 2), (2, 2, 3)]
    degree = 512
    records = []
    for p, q, m in cases:
        budget = Budget()
        module = fixed_iterate(p, q, m, budget)
        direct = direct_coefficients(p, q, m, degree)
        computed = [module.coefficient(n) for n in range(degree + 1)]
        if direct != computed:
            n = next(i for i in range(degree + 1) if direct[i] != computed[i])
            raise AssertionError((p, q, m, n, direct[n], computed[n]))
        records.append({
            "p": p, "q": q, "m": m, "checked_indices": [0, degree],
            "comparisons": degree + 1, "passed": True,
            "setup_work_units": budget.work,
            "first_24_coefficients": computed[:24],
            **module.statistics(),
        })
    return {
        "method": "Exact modular comparison with independent truncated Cauchy composition",
        "scope": "Four fixed-depth modules; finite verification supplements the proof",
        "total_comparisons": sum(r["comparisons"] for r in records),
        "cases": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-p", "--prime", type=int, default=2)
    parser.add_argument("-q", "--exponent", type=int, default=2)
    parser.add_argument("-m", "--iterations", type=int, default=2)
    parser.add_argument("-n", "--index", type=int, default=100)
    parser.add_argument("--export", type=Path)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--verification-output", type=Path)
    parser.add_argument("--max-dimension", type=int, default=1000)
    parser.add_argument("--max-terms", type=int, default=200_000)
    parser.add_argument("--max-work", type=int, default=10_000_000)
    parser.add_argument("--max-radix", type=int, default=257)
    args = parser.parse_args()
    try:
        if args.verify:
            result = verify()
            if args.verification_output:
                args.verification_output.parent.mkdir(parents=True, exist_ok=True)
                args.verification_output.write_text(json.dumps(result, indent=2) + "\n")
        else:
            budget = Budget(args.max_dimension, args.max_terms,
                            args.max_work, args.max_radix)
            module = fixed_iterate(args.prime, args.exponent, args.iterations, budget)
            result = {
                "p": args.prime, "q": args.exponent, "m": args.iterations,
                "index": args.index, "coefficient_mod_p_to_q": module.coefficient(args.index),
                "setup_work_units": budget.work, **module.statistics(),
            }
            if args.export:
                args.export.write_text(json.dumps(module.export(), indent=2) + "\n")
    except (ValueError, AssertionError) as error:
        parser.exit(2, f"cartier.py: {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
