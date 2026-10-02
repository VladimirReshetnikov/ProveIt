#!/usr/bin/env python3
"""Canonical compact cubic certificates for explicit periodic-plus-finite inputs.

A finite periodic table is required; there is no implicit oracle for heights.
A box radius is a compiler parameter, NOT a quantified polynomial variable.
This module does not implement Cairns's Turing-machine input loader.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import prod
from typing import Any, Mapping

import sandpile_compact as compact
from sandpile_cubic import Graph, box_graph, natural


@dataclass(frozen=True)
class PeriodicInput:
    """Stable periodic background with finitely many nonnegative replacements.

    The flat background table is in lexicographic product order. Overrides
    are ((coordinate_tuple, replacement_height), ...), not added increments.
    """
    periods: tuple[int, ...]
    background: tuple[int, ...]
    overrides: tuple[tuple[tuple[int, ...], int], ...] = ()

    def __post_init__(self) -> None:
        if not self.periods or any(type(p) is not int or p < 1 for p in self.periods):
            raise ValueError("periods must be positive Python integers")
        if len(self.background) != prod(self.periods):
            raise ValueError("periodic table has wrong size")
        for value in self.background:
            if natural(value, "background height") >= 2*self.dimension:
                raise ValueError("the periodic background must be stable")
        seen = set()
        for x, value in self.overrides:
            if (not isinstance(x, tuple) or len(x) != self.dimension
                    or any(type(v) is not int for v in x) or x in seen):
                raise ValueError("override coordinates must be distinct integer tuples")
            natural(value, "replacement height")
            seen.add(x)

    @property
    def dimension(self) -> int:
        return len(self.periods)

    @property
    def defect_radius(self) -> int:
        return max((abs(v) for x, _ in self.overrides for v in x), default=0)

    def height(self, x: tuple[int, ...]) -> int:
        if len(x) != self.dimension or any(type(v) is not int for v in x):
            raise ValueError("coordinate has wrong dimension or noninteger entries")
        for y, value in self.overrides:
            if x == y:
                return value
        index = 0
        for v, period in zip(x, self.periods):
            index = index*period + v % period
        return self.background[index]


def neighbors(x: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    result = []
    for axis in range(len(x)):
        for step in (-1, 1):
            y = list(x)
            y[axis] += step
            result.append(tuple(y))
    return tuple(result)


@dataclass(frozen=True)
class SpatialInstance:
    source: PeriodicInput
    radius: int
    minimum_radius: int
    graph: Graph
    sites: tuple[tuple[int, ...], ...]
    collar: tuple[tuple[int, ...], ...]

    @classmethod
    def build(cls, source: PeriodicInput, radius: int,
              minimum_radius: int | None = None) -> SpatialInstance:
        natural(radius, "radius")
        R0 = source.defect_radius if minimum_radius is None else natural(minimum_radius, "R0")
        if R0 < source.defect_radius or radius < R0:
            raise ValueError("require radius >= R0 >= defect radius")
        graph, sites = box_graph(source.dimension, radius)
        inside = set(sites)
        collar = tuple(sorted({y for x in sites for y in neighbors(x)}-inside))
        return cls(source, radius, R0, graph, sites, collar)

    @property
    def eta(self) -> tuple[int, ...]:
        return tuple(self.source.height(x) for x in self.sites)

    def names(self) -> tuple[str, ...]:
        return compact.names(self.graph) + tuple(f"collar_{i}" for i in range(len(self.collar))) + ("rho",)

    def polynomial_terms(self, w: Mapping[str, Any]) -> list[Any]:
        terms = compact.polynomial_terms(self.graph, self.eta, w)
        index = {x: i for i, x in enumerate(self.sites)}
        threshold = 2*self.source.dimension
        for i, x in enumerate(self.collar):
            influx = sum(w[f"u_{index[y]}"] for y in neighbors(x) if y in index)
            terms.append((self.source.height(x)+influx+w[f"collar_{i}"]-threshold+1)**2)
        if self.radius == self.minimum_radius:
            terms.append(w["rho"]**2)
        else:
            active = sum(w[f"k_{v}"]+w[f"c_{v}"] for v, x in enumerate(self.sites)
                         if max(map(abs, x)) == self.radius)
            terms.append((active-1-w["rho"])**2)
        return terms

    def evaluate(self, w: Mapping[str, int]) -> int:
        if set(w) != set(self.names()):
            raise ValueError("missing or extra spatial certificate coordinates")
        for name, value in w.items():
            natural(value, name)
        return sum(self.polynomial_terms(w))

    def certificate(self) -> dict[str, int]:
        w = compact.certificate(self.graph, self.eta)
        index = {x: i for i, x in enumerate(self.sites)}
        threshold = 2*self.source.dimension
        for i, x in enumerate(self.collar):
            influx = sum(w[f"u_{index[y]}"] for y in neighbors(x) if y in index)
            gap = threshold-1-self.source.height(x)-influx
            if gap < 0:
                raise ValueError("finite sink stabilization has an unstable exterior collar")
            w[f"collar_{i}"] = gap
        if self.radius == self.minimum_radius:
            w["rho"] = 0
        else:
            active = sum(w[f"k_{v}"]+w[f"c_{v}"] for v, x in enumerate(self.sites)
                         if max(map(abs, x)) == self.radius)
            if active == 0:
                raise ValueError("closed box is larger than the canonical radius")
            w["rho"] = active-1
        if self.evaluate(w) != 0:
            raise AssertionError("constructed spatial certificate is nonzero")
        return w

    def symbolic_polynomial(self) -> Any:
        try:
            import sympy as sp
        except ImportError as exc:
            raise RuntimeError("symbolic export requires SymPy") from exc
        xs = tuple(sp.Symbol(name) for name in self.names())
        return sp.Poly(sp.expand(sum(self.polynomial_terms(dict(zip(self.names(), xs))))),
                       *xs, domain=sp.ZZ)


if __name__ == "__main__":
    source = PeriodicInput((1,), (0,), (((0,), 12),))
    instance = SpatialInstance.build(source, 5)
    witness = instance.certificate()
    print("canonical radius:", instance.radius)
    print("certificate coordinates:", len(witness))
    print("exact polynomial value:", instance.evaluate(witness))
