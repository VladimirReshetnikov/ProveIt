#!/usr/bin/env python3
"""Exact quadratic transition compiler for natural-number counter networks.

Python 3.10+, standard library only.  A monomial is a sorted tuple of variable
indices; the empty tuple denotes 1.  Variables are all source-state coordinates
followed by all target-state coordinates.  No existential variables occur.

Usage:
  python code/quadratic_compiler.py examples/finite_visits.json --output out.json
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Iterable, Mapping
import argparse
import json

Polynomial = dict[tuple[int, ...], int]


def add_term(poly: Polynomial, monomial: tuple[int, ...], coefficient: int) -> None:
    key = tuple(sorted(monomial))
    value = poly.get(key, 0) + coefficient
    if value:
        poly[key] = value
    else:
        poly.pop(key, None)


def add_square(poly: Polynomial, linear: Mapping[int | None, int]) -> None:
    """Add the square of an affine form (None indexes its constant)."""
    for i, a in linear.items():
        for j, b in linear.items():
            monomial = tuple(k for k in (i, j) if k is not None)
            add_term(poly, monomial, a * b)


def evaluate(poly: Mapping[tuple[int, ...], int], values: tuple[int, ...]) -> int:
    ans = 0
    for monomial, coefficient in poly.items():
        term = coefficient
        for i in monomial:
            term *= values[i]
        ans += term
    return ans


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    kind: str
    counter: int | None = None
    label: str = ""

    def delta(self, j: int) -> int:
        if self.counter != j:
            return 0
        return {"inc": 1, "dec": -1}.get(self.kind, 0)


@dataclass(frozen=True)
class Machine:
    controls: tuple[str, ...]
    counters: int
    edges: tuple[Edge, ...]
    marked: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not self.controls or len(set(self.controls)) != len(self.controls):
            raise ValueError("Controls must be a nonempty tuple of distinct names")
        if self.counters < 0:
            raise ValueError("Counter count must be nonnegative")
        q = len(self.controls)
        for edge in self.edges:
            if not (0 <= edge.source < q and 0 <= edge.target < q):
                raise ValueError("Edge endpoint is out of range")
            if edge.kind not in {"inc", "dec", "zero", "nop"}:
                raise ValueError(f"Unknown edge kind: {edge.kind}")
            if edge.kind == "nop":
                if edge.counter is not None:
                    raise ValueError("NOP must not specify a counter")
            elif edge.counter is None or not 0 <= edge.counter < self.counters:
                raise ValueError("INC/DEC/ZERO must specify a valid counter")
        if any(not 0 <= a < q for a in self.marked):
            raise ValueError("Marked control is out of range")

    @property
    def dimension(self) -> int:
        return len(self.controls) + self.counters + len(self.edges)

    @property
    def syntactic_branch_bound(self) -> int:
        return max(sum(e.source == i for e in self.edges)
                   for i in range(len(self.controls)))

    def state(self, control: int, counters: Iterable[int],
              previous_edge: int | None = None) -> tuple[int, ...]:
        xs = tuple(counters)
        if not 0 <= control < len(self.controls):
            raise ValueError("Invalid control")
        if len(xs) != self.counters or any(type(x) is not int or x < 0 for x in xs):
            raise ValueError("Wrong counter tuple")
        p = tuple(int(i == control) for i in range(len(self.controls)))
        h = tuple(int(i == previous_edge) for i in range(len(self.edges)))
        if previous_edge is not None and not 0 <= previous_edge < len(self.edges):
            raise ValueError("Invalid previous edge")
        return p + xs + h

    def valid_natural_state(self, s: tuple[int, ...]) -> bool:
        return len(s) == self.dimension and all(type(x) is int and x >= 0 for x in s)

    def successors(self, source: tuple[int, ...]) -> list[tuple[int, ...]]:
        if not self.valid_natural_state(source):
            raise ValueError("State must be a natural tuple of the right dimension")
        q = len(self.controls)
        p, xs = source[:q], source[q:q + self.counters]
        if sum(p) != 1:
            return []
        control = p.index(1)
        result = []
        for a, edge in enumerate(self.edges):
            if edge.source != control:
                continue
            ys = list(xs)
            j = edge.counter
            if edge.kind == "zero" and xs[j] != 0:
                continue
            if edge.kind == "dec":
                if xs[j] == 0:
                    continue
                ys[j] -= 1
            if edge.kind == "inc":
                ys[j] += 1
            result.append(self.state(edge.target, ys, a))
        return result

    def marked_state(self, s: tuple[int, ...]) -> bool:
        return any(s[i] == 1 for i in self.marked)

    def energy(self, source: tuple[int, ...], target: tuple[int, ...]) -> int:
        """Evaluate the factored polynomial independently of sparse expansion."""
        if not self.valid_natural_state(source) or not self.valid_natural_state(target):
            raise ValueError("Expected two natural states")
        q, r = len(self.controls), self.counters
        p, x = source[:q], source[q:q+r]
        pp, xx, e = target[:q], target[q:q+r], target[q+r:]
        value = (sum(e) - 1) ** 2
        for i in range(q):
            value += (p[i] - sum(e[a] for a, ed in enumerate(self.edges)
                                 if ed.source == i)) ** 2
            value += (pp[i] - sum(e[a] for a, ed in enumerate(self.edges)
                                  if ed.target == i)) ** 2
        for j in range(r):
            value += (xx[j] - x[j] - sum(ed.delta(j) * e[a]
                       for a, ed in enumerate(self.edges))) ** 2
        value += sum(e[a] * x[ed.counter] for a, ed in enumerate(self.edges)
                     if ed.kind == "zero")
        return value

    def compile(self) -> Polynomial:
        q, r, m, d = len(self.controls), self.counters, len(self.edges), self.dimension
        sel = lambda a: d + q + r + a
        poly: Polynomial = {}
        add_square(poly, {None: -1, **{sel(a): 1 for a in range(m)}})
        for i in range(q):
            add_square(poly, {i: 1, **{sel(a): -1 for a, ed in enumerate(self.edges)
                                      if ed.source == i}})
            add_square(poly, {d+i: 1, **{sel(a): -1 for a, ed in enumerate(self.edges)
                                        if ed.target == i}})
        for j in range(r):
            form: dict[int | None, int] = {d+q+j: 1, q+j: -1}
            for a, ed in enumerate(self.edges):
                if ed.delta(j):
                    form[sel(a)] = -ed.delta(j)
            add_square(poly, form)
        for a, ed in enumerate(self.edges):
            if ed.kind == "zero":
                add_term(poly, (sel(a), q+ed.counter), 1)
        return poly

    def variable_names(self) -> list[str]:
        local = ([f"p_{i}" for i in range(len(self.controls))]
                 + [f"x_{j}" for j in range(self.counters)]
                 + [f"h_{a}" for a in range(len(self.edges))])
        return local + [v + "_next" for v in local]

    @classmethod
    def from_dict(cls, data: dict) -> Machine:
        return cls(tuple(data["controls"]), int(data["counters"]),
                   tuple(Edge(**e) for e in data["edges"]),
                   tuple(data.get("marked", ())))

    def export(self) -> dict:
        poly = self.compile()
        return {
            "state_dimension": self.dimension,
            "polynomial_variables": 2*self.dimension,
            "branch_bound": self.syntactic_branch_bound,
            "degree": max(map(len, poly), default=0),
            "coefficient_height": max(map(abs, poly.values()), default=0),
            "monomial_count": len(poly),
            "variable_names": self.variable_names(),
            "terms": [{"monomial": list(k), "coefficient": v}
                      for k, v in sorted(poly.items(), key=lambda kv: (len(kv[0]), kv[0]))],
            "domain": "All source and target coordinates are nonnegative integers.",
            "existential_auxiliary_variables": 0,
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("machine", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        machine = Machine.from_dict(json.loads(args.machine.read_text(encoding="utf-8")))
        text = json.dumps(machine.export(), indent=2) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
