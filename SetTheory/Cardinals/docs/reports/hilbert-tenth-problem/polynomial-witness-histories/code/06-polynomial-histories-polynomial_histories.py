#!/usr/bin/env python3
"""Exact, dependency-free compiler for unique CA histories over N[X,Y].

All equations are affine-linear in polynomial unknowns.  Polynomial equality
is coefficientwise; numerical evaluation of X and Y is NOT the semantics.
Run verification.py for exhaustive and adversarial checks.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping, Sequence

Exponent = tuple[int, int]
Poly = dict[Exponent, int]
ZERO: Poly = {}
ONE: Poly = {(0, 0): 1}


def monomial(x: int = 0, y: int = 0, coefficient: int = 1) -> Poly:
    if x < 0 or y < 0:
        raise ValueError("Polynomial exponents must be nonnegative.")
    return {(x, y): coefficient} if coefficient else {}


def add(*polys: Mapping[Exponent, int]) -> Poly:
    result: Poly = {}
    for poly in polys:
        for exponent, coefficient in poly.items():
            result[exponent] = result.get(exponent, 0) + coefficient
            if result[exponent] == 0:
                del result[exponent]
    return result


def scale(poly: Mapping[Exponent, int], coefficient: int) -> Poly:
    return {e: coefficient * c for e, c in poly.items() if coefficient * c}


def shift(poly: Mapping[Exponent, int], x: int = 0, y: int = 0) -> Poly:
    if x < 0 or y < 0:
        raise ValueError("Negative shifts are not supported.")
    return {(i + x, j + y): c for (i, j), c in poly.items()}


def multiply(left: Mapping[Exponent, int], right: Mapping[Exponent, int]) -> Poly:
    result: Poly = {}
    for (i, j), a in left.items():
        for (k, ell), b in right.items():
            exponent = (i + k, j + ell)
            result[exponent] = result.get(exponent, 0) + a * b
            if not result[exponent]:
                del result[exponent]
    return result


def repunit(length: int, y: int = 0) -> Poly:
    if length < 0:
        raise ValueError("Negative repunit length.")
    return {(j, y): 1 for j in range(length)}


def encode_poly(poly: Mapping[Exponent, int]) -> list[list[int]]:
    return [[i, j, c] for (i, j), c in sorted(poly.items(), key=lambda z: (z[0][1], z[0][0]))]


def is_natural(poly: Mapping[Exponent, int]) -> bool:
    return all(isinstance(i, int) and isinstance(j, int) and i >= 0 and j >= 0
               and isinstance(c, int) and c >= 0 for (i, j), c in poly.items())


def is_boolean(poly: Mapping[Exponent, int]) -> bool:
    return is_natural(poly) and all(c in (0, 1) for c in poly.values())


@dataclass(frozen=True)
class CA:
    """Alphabet is range(size); 0 is the quiescent blank symbol."""
    size: int
    table: Mapping[tuple[int, int, int], int]
    accepting: frozenset[int]

    def __post_init__(self) -> None:
        if self.size < 1:
            raise ValueError("The alphabet must be nonempty.")
        expected = set(product(range(self.size), repeat=3))
        if set(self.table) != expected:
            raise ValueError("The rule must supply exactly all alphabet triples.")
        if any(not isinstance(a, int) or not 0 <= a < self.size for a in self.table.values()):
            raise ValueError("Rule output outside the alphabet.")
        if self.table[(0, 0, 0)] != 0:
            raise ValueError("The blank must be quiescent.")
        if 0 in self.accepting or not self.accepting <= frozenset(range(self.size)):
            raise ValueError("Acceptance must exclude the blank and use valid symbols.")
        # Copy mutable caller data: a later mutation cannot change the CA semantics.
        from types import MappingProxyType
        object.__setattr__(self, "table", MappingProxyType(dict(self.table)))
        object.__setattr__(self, "accepting", frozenset(self.accepting))

    def validate_word(self, word: Sequence[int]) -> tuple[int, ...]:
        value = tuple(word)
        if not value or any(not isinstance(a, int) or not 0 <= a < self.size for a in value):
            raise ValueError("Input must be a nonempty word over the alphabet.")
        return value

    def step(self, word: Sequence[int]) -> tuple[int, ...]:
        old = self.validate_word(word)
        padded = (0, 0) + old + (0, 0)
        return tuple(self.table[tuple(padded[j:j + 3])] for j in range(len(old) + 2))


@dataclass
class LinearEquation:
    name: str
    coefficients: dict[str, Poly]
    constant: Poly

    def residual(self, witness: Mapping[str, Poly]) -> Poly:
        result = dict(self.constant)
        for name, coefficient in self.coefficients.items():
            result = add(result, multiply(coefficient, witness[name]))
        return result

    def serializable(self) -> dict:
        return {"name": self.name, "constant": encode_poly(self.constant),
                "coefficients": {k: encode_poly(v) for k, v in self.coefficients.items()}}


@dataclass
class CompiledSystem:
    ca: CA
    word: tuple[int, ...]
    variables: tuple[str, ...]
    equations: tuple[LinearEquation, ...]

    def residuals(self, witness: Mapping[str, Poly]) -> dict[str, Poly]:
        if set(witness) != set(self.variables):
            raise ValueError("Witness keys must be exactly the compiled variable names.")
        if not all(is_natural(p) for p in witness.values()):
            raise ValueError("Witness polynomials must have nonnegative integer coefficients.")
        return {e.name: value for e in self.equations if (value := e.residual(witness))}

    def serializable(self) -> dict:
        return {"domain": "N[X,Y]", "semantics": "coefficientwise polynomial equality",
                "alphabet_size": self.ca.size, "word": list(self.word),
                "accepting": sorted(self.ca.accepting), "variables": list(self.variables),
                "rule_table": [[*key, value] for key, value in sorted(self.ca.table.items())],
                "equations": [e.serializable() for e in self.equations]}


def tile_name(triple: tuple[int, int, int]) -> str:
    return "Z_" + "_".join(map(str, triple))


def compile_system(ca: CA, word: Sequence[int], *, horizontal: str = "marginal") -> CompiledSystem:
    """Return the COMPLETE system, including clocks and first acceptance.

    Variable count s^3+s+5; equation count 3s+3 in the default marginal
    compiler, or s^2+s+4 with horizontal="pair". The two compilers have
    exactly the same full natural-polynomial zero set. Their matrices are
    independent of word and word length; only constant vectors encode input.
    """
    word = ca.validate_word(word)
    m, s = len(word), ca.size
    triples = tuple(product(range(s), repeat=3))
    variables = ("D", "Q", "B", "V", "J") + tuple(map(tile_name, triples)) + tuple(f"T_{a}" for a in range(s))
    equations: list[LinearEquation] = []

    def row(name: str, terms: Iterable[tuple[str, Poly]], constant: Poly | None = None) -> None:
        coefficients: dict[str, Poly] = {}
        for key, coefficient in terms:
            coefficients[key] = add(coefficients.get(key, {}), coefficient)
        coefficients = {key: value for key, value in coefficients.items() if value}
        equations.append(LinearEquation(name, coefficients, constant or {}))

    row("clock_right", [("D", ONE), ("Q", add(ONE, monomial(2, 1, -1)))], monomial(m + 1, 0, -1))
    row("clock_time", [("B", ONE), ("V", add(ONE, monomial(0, 1, -1)))], scale(ONE, -1))
    if horizontal not in ("marginal", "pair"):
        raise ValueError('horizontal must be "marginal" or "pair".')
    if horizontal == "pair":
        for a, b in product(range(s), repeat=2):
            terms: list[tuple[str, Poly]] = []
            for ell, c, r in triples:
                z = tile_name((ell, c, r))
                if (c, r) == (a, b):
                    terms.append((z, monomial(1)))
                if (ell, c) == (a, b):
                    terms.append((z, scale(ONE, -1)))
            if (a, b) == (0, 0):
                terms += [("V", ONE), ("Q", monomial(1, 0, -1))]
            row(f"horizontal_{a}_{b}", terms)
    else:
        for a in range(s):
            terms = []
            for ell, c, r in triples:
                z = tile_name((ell, c, r))
                if c == a:
                    terms.append((z, monomial(1)))
                if ell == a:
                    terms.append((z, scale(ONE, -1)))
            if a == 0:
                terms += [("V", ONE), ("Q", monomial(1, 0, -1))]
            row(f"left_marginal_{a}", terms)
        for a in range(1, s):
            terms = []
            for ell, c, r in triples:
                z = tile_name((ell, c, r))
                if r == a:
                    terms.append((z, monomial(1)))
                if c == a:
                    terms.append((z, scale(ONE, -1)))
            row(f"right_marginal_{a}", terms)
    for a in range(s):
        terms = [(f"T_{a}", ONE)]
        for triple in triples:
            if triple[1] == a:
                terms.append((tile_name(triple), ONE))
            if ca.table[triple] == a:
                terms.append((tile_name(triple), monomial(1, 1, -1)))
        if a == 0:
            terms += [(key, scale(ONE, -1)) for key in ("V", "B", "Q", "D")]
        initial = {(j + 1, 0): -1 for j, symbol in enumerate(word) if symbol == a}
        row(f"vertical_{a}", terms, initial)
    row("no_early_acceptance", [(tile_name(triple), ONE) for triple in triples if triple[1] in ca.accepting])
    row("one_final_acceptance", [(f"T_{a}", ONE) for a in sorted(ca.accepting)] +
        [("J", add(ONE, monomial(1, 0, -1))), ("B", scale(ONE, -1))])
    assert len(variables) == s ** 3 + s + 5
    assert len(equations) == (3*s + 3 if horizontal == "marginal" else s*s+s+4)
    return CompiledSystem(ca, word, variables, tuple(equations))


def witness_for_horizon(system: CompiledSystem, h: int) -> tuple[dict[str, Poly], list[tuple[int, ...]]]:
    """Build the deterministic tableau up to h; acceptance may fail.

    All non-acceptance equations always hold.  J is canonical when the last
    row has one accepting cell and is set to zero otherwise, so a failed
    acceptance test never silently produces a claimed certificate.
    """
    if not isinstance(h, int) or h < 0:
        raise ValueError("Horizon must be a nonnegative integer.")
    ca, m = system.ca, len(system.word)
    witness = {v: {} for v in system.variables}
    witness["D"] = monomial(m + 1 + 2 * h, h)
    witness["Q"] = {(m + 1 + 2 * t, t): 1 for t in range(h)}
    witness["B"] = monomial(0, h)
    witness["V"] = {(0, t): 1 for t in range(h)}
    history = [system.word]
    old = system.word
    for t in range(h):
        padded = (0, 0) + old + (0, 0)
        new = []
        for j in range(len(old) + 2):
            triple = tuple(padded[j:j + 3])
            witness[tile_name(triple)][(j, t)] = 1
            new.append(ca.table[triple])
        old = tuple(new)
        history.append(old)
    top = (0,) + old + (0,)
    for j, a in enumerate(top):
        witness[f"T_{a}"][(j, h)] = 1
    accepts = [j for j, a in enumerate(top) if a in ca.accepting]
    if len(accepts) == 1:
        witness["J"] = repunit(accepts[0], h)
    return witness, history


def is_first_single_acceptance(ca: CA, history: Sequence[Sequence[int]]) -> bool:
    counts = [sum(a in ca.accepting for a in word) for word in history]
    return bool(counts) and counts[-1] == 1 and not any(counts[:-1])


def witness_statistics(witness: Mapping[str, Poly]) -> dict[str, int | bool]:
    support = [e for p in witness.values() for e, c in p.items() if c]
    return {"boolean_coefficients": all(is_boolean(p) for p in witness.values()),
            "total_nonzero_coefficients": len(support),
            "max_X_degree": max((i for i, _ in support), default=-1),
            "max_Y_degree": max((j for _, j in support), default=-1),
            "max_total_degree": max((i + j for i, j in support), default=-1)}


def elementary_ca(rule_number: int) -> CA:
    if not 0 <= rule_number < 256 or rule_number & 1:
        raise ValueError("Use a binary elementary rule with quiescent 000 (even rule number).")
    return CA(2, {t: (rule_number >> (4 * t[0] + 2 * t[1] + t[2])) & 1
                  for t in product(range(2), repeat=3)}, frozenset({1}))


def example_ca() -> CA:
    """A moving signal becomes accepting on encountering a stationary mark.

    0 blank, 1 right-moving signal, 2 mark, 3 accepting signal.
    This small illustrative rule is NOT asserted to be universal.
    """
    def rule(t: tuple[int, int, int]) -> int:
        ell, c, r = t
        if c == 3:
            return 3
        if c == 2 and ell == 1:
            return 3
        if c == 2:
            return 2
        if c == 0 and ell == 1:
            return 1
        return 0
    return CA(4, {t: rule(t) for t in product(range(4), repeat=3)}, frozenset({3}))


def compile_feature_system(ca: CA, word: Sequence[int], *,
                           features: Sequence[Sequence[int]] | None = None) -> CompiledSystem:
    """Same full natural zero set via injective nonnegative symbol features.

    Default: binary digits, d = ceil(log2(s)), 6+3*d equations, coefficient
    magnitude <= 1. Passing features=[(a,) for a in range(s)] gives nine
    equations with coefficient magnitude <= max(1,s-1). Unknowns are unchanged.
    """
    base = compile_system(ca, word)
    s, m = ca.size, len(base.word)
    if features is None:
        d = (s-1).bit_length()
        feature_tuple = tuple(tuple((a >> k) & 1 for k in range(d)) for a in range(s))
    else:
        feature_tuple = tuple(tuple(row) for row in features)
        if len(feature_tuple) != s:
            raise ValueError("There must be exactly one feature vector per symbol.")
        d = len(feature_tuple[0])
    if (any(len(row) != d for row in feature_tuple)
        or any(not isinstance(c, int) or c < 0 for row in feature_tuple for c in row)
        or any(feature_tuple[0]) or len(set(feature_tuple)) != s):
        raise ValueError("Features must be nonnegative, equally sized, injective, and zero on blank.")
    triples = tuple(product(range(s), repeat=3))
    equations = list(base.equations[:2])

    def row(name, terms, constant=None):
        coefficients = {}
        for key, coefficient in terms:
            coefficients[key] = add(coefficients.get(key, {}), coefficient)
        equations.append(LinearEquation(name, {k: p for k,p in coefficients.items() if p}, constant or {}))

    row("total_shape", [(tile_name(t), add(monomial(1), scale(ONE, -1))) for t in triples]
        + [("V", ONE), ("Q", monomial(1, 0, -1))])
    for k in range(d):
        left_terms, right_terms = [], []
        for t in triples:
            ell, c, r = t
            left_terms.append((tile_name(t), add(monomial(1, 0, feature_tuple[c][k]),
                                                 monomial(0, 0, -feature_tuple[ell][k]))))
            right_terms.append((tile_name(t), add(monomial(1, 0, feature_tuple[r][k]),
                                                  monomial(0, 0, -feature_tuple[c][k]))))
        row(f"feature_left_{k}", left_terms)
        row(f"feature_right_{k}", right_terms)
    row("total_vertical",
        [(tile_name(t), add(ONE, monomial(1, 1, -1))) for t in triples]
        + [(f"T_{a}", ONE) for a in range(s)]
        + [(key, scale(ONE, -1)) for key in ("D", "Q", "B", "V")],
        {(j+1, 0): -1 for j in range(m)})
    for k in range(d):
        terms = [(tile_name(t), add(monomial(0, 0, feature_tuple[t[1]][k]),
                                  monomial(1, 1, -feature_tuple[ca.table[t]][k]))) for t in triples]
        terms += [(f"T_{a}", monomial(0, 0, feature_tuple[a][k])) for a in range(s)]
        initial = {(j+1, 0): -feature_tuple[a][k] for j, a in enumerate(base.word) if feature_tuple[a][k]}
        row(f"feature_vertical_{k}", terms, initial)
    equations += list(base.equations[-2:])
    assert len(equations) == 6+3*d
    return CompiledSystem(ca, base.word, base.variables, tuple(equations))
