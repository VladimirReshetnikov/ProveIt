#!/usr/bin/env python3
"""Exact finite prototype of the Cauchy mode identity and rank encoding.

This module is NOT a SAT solver and does NOT implement an improved asymptotic
contraction algorithm.  It checks one packet of the published deformation over
Z/(2**precision), using integer interpolation values rather than an extension
ring.  Two groups are enough to verify the algebra and the compressed-index
construction.  No collision-packing or Hermite-recovery claim is tested here.

All arithmetic is exact.  Fractions are reduced modulo a power of two only
after checking that their reduced denominator is odd.  Cauchy entries at grid
roots are evaluated as polynomials with the canceled factor omitted, so the
code never evaluates an artificial 0/0 expression.

Source: OpenAI, The Exponential Time Hypothesis is False, October 25, 2026,
commit 42907c9e999cc00d6abe7a50bfc1023250edd1b9,
quantitative-contraction.tex, equations tensor-cauchy,
tensor-mode-expansion, and tensor-recursion-identity.

Standard library only; Python 3.10 or newer.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod
from random import Random
from typing import Iterator, Sequence


def valuation_two(value: int | Fraction) -> int | float:
    """Return v_2(value), using positive infinity for zero."""
    value = Fraction(value)
    if not value:
        return float("inf")

    def integer_valuation(integer: int) -> int:
        integer = abs(integer)
        return (integer & -integer).bit_length() - 1

    return integer_valuation(value.numerator) - integer_valuation(value.denominator)


def fraction_mod(value: int | Fraction, precision: int) -> int:
    """Reduce a two-adically integral rational modulo 2**precision."""
    if precision < 1:
        raise ValueError("precision must be positive")
    value = Fraction(value)
    if value.denominator % 2 == 0:
        raise ValueError("fraction is not two-adically integral")
    modulus = 1 << precision
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def bit_assignments(length: int) -> Iterator[tuple[int, ...]]:
    return product((0, 1), repeat=length)


class WeightedTuples:
    """Exact-weight nonnegative tuples, ordered lexicographically.

    A word (b_0,...,b_(d-1)) belongs to this finite set iff
    sum(weights[j] * b_j) == total_weight.  Completion counts support exact
    rank/unrank and explicitly padded Boolean encodings.  This small prototype
    uses an iterative dynamic-programming table; it is not an assertion about
    the optimal asymptotic implementation of coefficient extraction.
    """

    def __init__(self, weights: Sequence[int], total_weight: int):
        self.weights = tuple(weights)
        self.total_weight = total_weight
        if total_weight < 0 or any(weight <= 0 for weight in self.weights):
            raise ValueError("weights must be positive and total nonnegative")
        dimension = len(self.weights)
        table = [[0] * (total_weight + 1) for _ in range(dimension + 1)]
        table[dimension][0] = 1
        for index in reversed(range(dimension)):
            weight = self.weights[index]
            for remaining in range(total_weight + 1):
                # The first term fixes exponent zero; the second adds one.
                table[index][remaining] = table[index + 1][remaining]
                if remaining >= weight:
                    table[index][remaining] += table[index][remaining - weight]
        self._table = table
        self.count = table[0][total_weight]
        self.bit_length = (self.count - 1).bit_length() if self.count else 0

    def rank(self, exponents: Sequence[int]) -> int:
        exponents = tuple(exponents)
        if len(exponents) != len(self.weights):
            raise ValueError("wrong tuple length")
        if any(not isinstance(value, int) or value < 0 for value in exponents):
            raise ValueError("exponents must be nonnegative integers")
        if sum(w * b for w, b in zip(self.weights, exponents)) != self.total_weight:
            raise ValueError("tuple does not have the specified exact weight")
        result = 0
        remaining = self.total_weight
        for index, exponent in enumerate(exponents):
            weight = self.weights[index]
            for smaller in range(exponent):
                result += self._table[index + 1][remaining - smaller * weight]
            remaining -= exponent * weight
        return result

    def unrank(self, rank: int) -> tuple[int, ...]:
        if not isinstance(rank, int) or not 0 <= rank < self.count:
            raise ValueError("rank is outside the valid range")
        remaining = self.total_weight
        result = []
        for index, weight in enumerate(self.weights):
            for exponent in range(remaining // weight + 1):
                completions = self._table[index + 1][remaining - exponent * weight]
                if rank < completions:
                    result.append(exponent)
                    remaining -= exponent * weight
                    break
                rank -= completions
            else:
                raise AssertionError("completion counts failed to decode rank")
        if remaining:
            raise AssertionError("unranking left unused weight")
        return tuple(result)

    def decode_bits(self, code: int) -> tuple[int, ...] | None:
        """Decode a fixed-width Boolean code; unused codes return None.

        A count-one family uses zero bits and its unique code is integer zero.
        A count-zero family has no valid encoding and is normally skipped.
        """
        if not isinstance(code, int) or not 0 <= code < (1 << self.bit_length):
            raise ValueError("code does not fit its fixed-width bit string")
        return self.unrank(code) if code < self.count else None

    def __iter__(self) -> Iterator[tuple[int, ...]]:
        for rank in range(self.count):
            yield self.unrank(rank)


def bounded_weight_tuples(weights: Sequence[int], strict_budget: int):
    """Enumerate every tuple of weighted degree less than strict_budget once."""
    for total_weight in range(strict_budget):
        yield from WeightedTuples(weights, total_weight)


@dataclass(frozen=True)
class Mode:
    tile: int
    order: int
    source: int
    target: int

    @property
    def weight(self) -> int:
        return self.order + 1


class CauchyPacket:
    """A fully occupied packet with two groups and exact small entry tables.

    Row group at slot x is bit_i(x), and column group at slot y is
    1-bit_i(y), where i=v_2(t).  Therefore W(t) is local: a surviving
    entry has y-x=t, which flips bit i.  All original group tensors are
    explicitly tabulated functions of their own row/column port bits.
    """

    def __init__(self, length: int, node: int, zeta: int, precision: int, seed: int):
        if length < 2 or length & (length - 1):
            raise ValueError("packet length must be a power of two >= 2")
        if not -length <= node < length or node == 0:
            raise ValueError("node must be a nonzero point of the packet grid")
        if precision < 1:
            raise ValueError("precision must be positive")
        self.length = length
        self.node = node
        self.zeta = zeta
        self.precision = precision
        self.seed = seed
        self.modulus = 1 << precision
        self.level = int(valuation_two(node))
        if (1 << self.level) >= length:
            raise ValueError("node valuation must address an existing slot bit")
        self.step = 1 << (self.level + 1)
        self.alpha = 2 * length
        self.argument = node + self.alpha * zeta
        self.grid = tuple(range(-length, length))
        self.derivative_zero = prod(-point for point in self.grid if point)
        self.row_ports = {
            group: tuple(x for x in range(length) if self.row_group(x) == group)
            for group in (0, 1)
        }
        self.column_ports = {
            group: tuple(y for y in range(length) if self.column_group(y) == group)
            for group in (0, 1)
        }
        self.modes = tuple(
            Mode(tile, order, self.column_group(tile), 1 - self.column_group(tile))
            for tile in range(self.step)
            for order in range(precision - 1)
        )
        self.weights = tuple(mode.weight for mode in self.modes)
        self.target_indices = {
            group: tuple(j for j, mode in enumerate(self.modes) if mode.target == group)
            for group in (0, 1)
        }
        self.source_indices = {
            group: tuple(j for j, mode in enumerate(self.modes) if mode.source == group)
            for group in (0, 1)
        }
        self.pair_indices = {
            pair: tuple(j for j, mode in enumerate(self.modes)
                        if (mode.source, mode.target) == pair)
            for pair in sorted({(mode.source, mode.target) for mode in self.modes})
        }
        self.matrix = tuple(
            tuple(fraction_mod(self.cauchy_entry(x, y, self.argument), precision)
                  for y in range(length))
            for x in range(length)
        )
        self.mode_coefficients = tuple(
            tuple(fraction_mod(self.mode_coefficient(x, mode), precision)
                  if self.row_group(x) == mode.target else 0
                  for mode in self.modes)
            for x in range(length)
        )
        rng = Random(seed)
        self.row_tables = {}
        self.column_tables = {}
        for group in (0, 1):
            self.row_tables[group] = {
                bits: rng.randint(-3, 4)
                for bits in bit_assignments(len(self.row_ports[group]))
            }
            self.column_tables[group] = {
                bits: rng.randint(-3, 4)
                for bits in bit_assignments(len(self.column_ports[group]))
            }

    def row_group(self, slot: int) -> int:
        return (slot >> self.level) & 1

    def column_group(self, slot: int) -> int:
        return 1 - ((slot >> self.level) & 1)

    def cauchy_entry(self, row: int, column: int, argument: int) -> Fraction:
        """Evaluate the canceled Cauchy polynomial, including at its roots."""
        omit = column - row
        if omit not in self.grid:
            raise ValueError("invalid packet slots")
        numerator = prod(argument - point for point in self.grid if point != omit)
        return Fraction(numerator, self.derivative_zero)

    def mode_coefficient(self, row: int, mode: Mode) -> Fraction:
        if self.row_group(row) != mode.target:
            return Fraction(0)
        denominator = self.argument - mode.tile + row
        if not denominator:
            raise AssertionError("a crossing tile cannot have a zero denominator")
        # The first factor is evaluated through the canceled polynomial.
        first = self.cauchy_entry(row, mode.tile, self.argument)
        return first * Fraction(self.step, denominator) ** mode.order

    def mode_linear_form(self, mode: Mode, column_bits: dict[int, int]) -> int:
        return sum(
            (index ** mode.order) * column_bits[column]
            for index, column in enumerate(range(mode.tile, self.length, self.step))
        ) % self.modulus

    def check_kernel_identity(self) -> dict[str, int]:
        """Verify the crossing expansion independently for every matrix entry."""
        crossing_entries = 0
        nonzero_crossing_entries = 0
        valuation_checks = 0
        for row in range(self.length):
            for column in range(self.length):
                if self.row_group(row) == self.column_group(column):
                    continue
                crossing_entries += 1
                total = 0
                for index, mode in enumerate(self.modes):
                    if column % self.step == mode.tile:
                        power_index = (column - mode.tile) // self.step
                        total += self.mode_coefficients[row][index] * power_index ** mode.order
                if total % self.modulus != self.matrix[row][column]:
                    raise AssertionError("truncated crossing expansion is incorrect")
                nonzero_crossing_entries += bool(self.matrix[row][column])
            for mode in self.modes:
                if self.row_group(row) == mode.target:
                    if valuation_two(self.mode_coefficient(row, mode)) < mode.weight:
                        raise AssertionError("mode coefficient violates divisibility budget")
                    valuation_checks += 1
        return {
            "crossing_entries_checked": crossing_entries,
            "nonzero_crossing_entries": nonzero_crossing_entries,
            "coefficient_valuation_checks": valuation_checks,
        }

    def direct_contraction(self) -> int:
        """Evaluate source F(T) by its independent sum over all X,Y bits."""
        total = 0
        for column_tuple in bit_assignments(self.length):
            column_weight = prod(
                self.column_tables[group][tuple(column_tuple[y] for y in self.column_ports[group])]
                for group in (0, 1)
            )
            forms = [sum(self.matrix[x][y] * column_tuple[y] for y in range(self.length))
                     % self.modulus for x in range(self.length)]
            for row_tuple in bit_assignments(self.length):
                row_weight = prod(
                    self.row_tables[group][tuple(row_tuple[x] for x in self.row_ports[group])]
                    for group in (0, 1)
                )
                value = row_weight * column_weight
                for row, bit in enumerate(row_tuple):
                    value *= forms[row] if bit else 1 - forms[row]
                    value %= self.modulus
                total = (total + value) % self.modulus
        return total

    def _row_polynomial(self, group: int, columns: dict[int, int], rows: dict[int, int]):
        """Multiply local affine row forms as a sparse mode polynomial."""
        targets = self.target_indices[group]
        local_weights = tuple(self.weights[index] for index in targets)
        zero = (0,) * len(targets)
        polynomial = {zero: 1}
        for row in self.row_ports[group]:
            local = sum(self.matrix[row][column] * bit for column, bit in columns.items())
            constant = local if rows[row] else 1 - local
            sign = 1 if rows[row] else -1
            updated: dict[tuple[int, ...], int] = {}
            for exponents, coefficient in polynomial.items():
                updated[exponents] = (updated.get(exponents, 0) + coefficient * constant) % self.modulus
                for local_index, global_index in enumerate(targets):
                    changed = list(exponents)
                    changed[local_index] += 1
                    if sum(w * b for w, b in zip(local_weights, changed)) >= self.precision:
                        continue
                    changed_tuple = tuple(changed)
                    contribution = coefficient * sign * self.mode_coefficients[row][global_index]
                    updated[changed_tuple] = (updated.get(changed_tuple, 0) + contribution) % self.modulus
            polynomial = {key: coefficient for key, coefficient in updated.items() if coefficient}
        return polynomial

    @lru_cache(maxsize=None)
    def group_contraction(self, group: int, exponents: tuple[int, ...]) -> int:
        """Compute the exact child Z_(group,beta) by summing its local bits."""
        if len(exponents) != len(self.modes):
            raise ValueError("wrong mode tuple length")
        requested = tuple(exponents[index] for index in self.target_indices[group])
        total = 0
        for column_tuple in bit_assignments(len(self.column_ports[group])):
            columns = dict(zip(self.column_ports[group], column_tuple))
            outgoing = 1
            for index in self.source_indices[group]:
                outgoing *= pow(self.mode_linear_form(self.modes[index], columns),
                                exponents[index], self.modulus)
                outgoing %= self.modulus
            if not outgoing:
                continue
            for row_tuple in bit_assignments(len(self.row_ports[group])):
                rows = dict(zip(self.row_ports[group], row_tuple))
                coefficient = self._row_polynomial(group, columns, rows).get(requested, 0)
                total += (self.row_tables[group][row_tuple]
                          * self.column_tables[group][column_tuple]
                          * coefficient * outgoing)
                total %= self.modulus
        return total

    def global_mode_contraction(self) -> tuple[int, dict[str, int]]:
        """Enumerate every feasible global beta and multiply its child values."""
        total = 0
        tuple_count = 0
        nonzero_terms = 0
        maximum_nonzero_mode_degree = 0
        for exponents in bounded_weight_tuples(self.weights, self.precision):
            tuple_count += 1
            value = prod(self.group_contraction(group, exponents) for group in (0, 1)) % self.modulus
            nonzero_terms += bool(value)
            if value:
                maximum_nonzero_mode_degree = max(maximum_nonzero_mode_degree, sum(exponents))
            total = (total + value) % self.modulus
        return total, {
            "feasible_mode_tuples": tuple_count,
            "nonzero_mode_terms": nonzero_terms,
            "maximum_nonzero_mode_degree": maximum_nonzero_mode_degree,
        }

    def compressed_rank_contraction(self) -> tuple[int, dict[str, int]]:
        """Contract pair-local binary rank indices, assigning zero to padding.

        Total weights are enumerated outside the network.  Within each fixed
        allocation, each directed pair has a binary index register shared by
        its two endpoint tensors.  Any unused bit pattern contributes zero.
        Equality-subdividing the registers would make the network bipartite
        without changing its value; such degree-two equality vertices are
        implicit here.  Nothing in this routine assumes a degree bound that
        would license the published fast contraction theorem on this network.
        """
        pairs = tuple(self.pair_indices)
        total = 0
        allocations = 0
        padded_indices = 0
        valid_indices = 0
        invalid_indices = 0
        maximum_wires = 0
        for allocation in bounded_weight_tuples((1,) * len(pairs), self.precision):
            families = [WeightedTuples(tuple(self.weights[index] for index in self.pair_indices[pair]), weight)
                        for pair, weight in zip(pairs, allocation)]
            if any(family.count == 0 for family in families):
                continue
            allocations += 1
            maximum_wires = max(maximum_wires, sum(family.bit_length for family in families))
            for codes in product(*(range(1 << family.bit_length) for family in families)):
                padded_indices += 1
                decoded = [family.decode_bits(code) for family, code in zip(families, codes)]
                if any(value is None for value in decoded):
                    invalid_indices += 1
                    continue  # Both endpoint tensors assign zero to invalid ranks.
                valid_indices += 1
                exponents = [0] * len(self.modes)
                for pair, part in zip(pairs, decoded):
                    assert part is not None
                    for index, exponent in zip(self.pair_indices[pair], part):
                        exponents[index] = exponent
                beta = tuple(exponents)
                value = prod(self.group_contraction(group, beta) for group in (0, 1))
                total = (total + value) % self.modulus
        return total, {
            "weight_allocations": allocations,
            "padded_binary_assignments": padded_indices,
            "valid_rank_assignments": valid_indices,
            "invalid_rank_assignments_given_zero": invalid_indices,
            "maximum_rank_bits_for_one_allocation": maximum_wires,
            "maximum_bits_after_equality_subdivision": 2 * maximum_wires,
        }


def verify_fixture(length: int, node: int, zeta: int, precision: int, seed: int) -> dict:
    """Compare three independently organized exact sums for one fixture."""
    packet = CauchyPacket(length, node, zeta, precision, seed)
    kernel_checks = packet.check_kernel_identity()
    direct = packet.direct_contraction()
    global_value, global_stats = packet.global_mode_contraction()
    rank_value, rank_stats = packet.compressed_rank_contraction()
    if not direct == global_value == rank_value:
        raise AssertionError(f"identity mismatch: {direct}, {global_value}, {rank_value}")
    if global_stats["feasible_mode_tuples"] != rank_stats["valid_rank_assignments"]:
        raise AssertionError("rank encoding duplicated or omitted a feasible mode tuple")
    result = {
        "length": length, "node": node, "zeta": zeta,
        "argument": packet.argument, "valuation_level": packet.level,
        "precision": precision, "modulus": packet.modulus, "seed": seed,
        "mode_count": len(packet.modes), "direct_bit_pairs": 1 << (2 * length),
        "direct_residue": direct, "global_mode_residue": global_value,
        "compressed_rank_residue": rank_value,
        "all_equal": True,
        **kernel_checks, **global_stats, **rank_stats,
    }
    # A cache per fixture is only a convenience for these tiny examples.
    packet.group_contraction.cache_clear()
    return result
