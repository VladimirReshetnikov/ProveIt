"""Polynomial-resource exact-weight tuple indexing used by the mode graph.

The dynamic program counts nonnegative exponent vectors. It does not store
the exponentially many vectors, and supports exact ranking and unranking.
All weights are positive integers, as they are for the Cauchy modes.
"""

from __future__ import annotations


class ExactWeightIndex:
    def __init__(self, weights: tuple[int, ...] | list[int], max_weight: int):
        if max_weight < 0 or any(not isinstance(w, int) or w <= 0 for w in weights):
            raise ValueError("weights must be positive integers and budget nonnegative")
        self.weights = tuple(weights)
        self.max_weight = max_weight
        v = len(self.weights)
        self.suffix = [[0] * (max_weight + 1) for _ in range(v + 1)]
        self.suffix[v][0] = 1
        for j in range(v - 1, -1, -1):
            weight = self.weights[j]
            for total in range(max_weight + 1):
                self.suffix[j][total] = self.suffix[j + 1][total]
                if total >= weight:
                    self.suffix[j][total] += self.suffix[j][total - weight]

    def count(self, total: int) -> int:
        if not 0 <= total <= self.max_weight:
            raise ValueError("total is outside the indexed range")
        return self.suffix[0][total]

    def unrank(self, total: int, index: int) -> tuple[int, ...]:
        if not 0 <= index < self.count(total):
            raise ValueError("index is outside the exact-weight list")
        budget = total
        result = []
        for j, weight in enumerate(self.weights):
            for exponent in range(budget // weight + 1):
                completions = self.suffix[j + 1][budget - exponent * weight]
                if index < completions:
                    result.append(exponent)
                    budget -= exponent * weight
                    break
                index -= completions
            else:
                raise ArithmeticError("inconsistent completion table")
        if budget or index:
            raise ArithmeticError("unranking did not consume the budget")
        return tuple(result)

    def rank(self, exponents: tuple[int, ...] | list[int]) -> tuple[int, int]:
        if len(exponents) != len(self.weights) or any(
                not isinstance(e, int) or e < 0 for e in exponents):
            raise ValueError("invalid exponent vector")
        total = sum(w * e for w, e in zip(self.weights, exponents))
        self.count(total)
        budget, index = total, 0
        for j, (weight, exponent) in enumerate(zip(self.weights, exponents)):
            for smaller in range(exponent):
                index += self.suffix[j + 1][budget - smaller * weight]
            budget -= exponent * weight
        return total, index

    def tuples(self, total: int):
        for index in range(self.count(total)):
            yield self.unrank(total, index)
