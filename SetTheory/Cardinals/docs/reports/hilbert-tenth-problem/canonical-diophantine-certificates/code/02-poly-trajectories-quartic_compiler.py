#!/usr/bin/env python3
"""Reference compiler from fixed-degree sign tables to a quartic equation.

The exported polynomial is specified exactly, without expansion, by
    P = sum(Q**2 for Q in residuals).
Every Q has degree at most two. Coefficients c_i are signed FREE parameters;
all existential variables are nonnegative integers. To make every parameter
natural, substitute c_i = c_i_plus - c_i_minus (free inputs, not witnesses).
The polynomial structure depends only on the nominal degree and the optional
nonnegativity assertion, never on the numerical coefficients or horizon.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import comb
from typing import Iterable
import argparse
import json
from certificates import Certificate, generate, padded


@dataclass(frozen=True)
class Polynomial:
    terms: tuple[tuple[tuple[str, ...], int], ...]

    @staticmethod
    def make(terms: dict[tuple[str, ...], int]) -> 'Polynomial':
        return Polynomial(tuple(sorted((m, c) for m, c in terms.items() if c)))

    @staticmethod
    def constant(value: int) -> 'Polynomial':
        return Polynomial.make({(): value})

    @staticmethod
    def variable(name: str) -> 'Polynomial':
        return Polynomial.make({(name,): 1})

    def __add__(self, other: 'Polynomial | int') -> 'Polynomial':
        other = convert(other)
        terms = dict(self.terms)
        for monomial, coefficient in other.terms:
            terms[monomial] = terms.get(monomial, 0) + coefficient
        return Polynomial.make(terms)

    __radd__ = __add__

    def __neg__(self) -> 'Polynomial':
        return Polynomial(tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other: 'Polynomial | int') -> 'Polynomial':
        return self + -convert(other)

    def __rsub__(self, other: 'Polynomial | int') -> 'Polynomial':
        return convert(other) + -self

    def __mul__(self, other: 'Polynomial | int') -> 'Polynomial':
        other = convert(other)
        terms: dict[tuple[str, ...], int] = {}
        for left, a in self.terms:
            for right, b in other.terms:
                monomial = tuple(sorted(left + right))
                terms[monomial] = terms.get(monomial, 0) + a * b
        return Polynomial.make(terms)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max((len(m) for m, _ in self.terms), default=0)

    def evaluate(self, values: dict[str, int]) -> int:
        total = 0
        for monomial, coefficient in self.terms:
            for name in monomial:
                coefficient *= values[name]
            total += coefficient
        return total

    def json(self) -> list[dict]:
        return [{'coefficient': c, 'variables': list(m)} for m, c in self.terms]


def convert(value: Polynomial | int) -> Polynomial:
    return value if isinstance(value, Polynomial) else Polynomial.constant(value)


class Compiler:
    def __init__(self) -> None:
        self.values: dict[str, int] = {}
        self.inputs: list[str] = []
        self.primary: list[str] = []
        self.auxiliary: list[str] = []
        self.residuals: list[Polynomial] = []
        self.labels: list[str] = []
        self.sign_cache: dict[Polynomial, tuple[Polynomial, Polynomial, Polynomial]] = {}
        self.wire_cache: dict[Polynomial, Polynomial] = {}

    def variable(self, name: str, value: int, category: str) -> Polynomial:
        if name in self.values:
            raise ValueError(f'Duplicate variable: {name}')
        self.values[name] = value
        getattr(self, category).append(name)
        return Polynomial.variable(name)

    def fresh(self, value: int) -> Polynomial:
        return self.variable(f'w{len(self.auxiliary)}', value, 'auxiliary')

    def residual(self, expression: Polynomial | int, label: str) -> None:
        expression = convert(expression)
        if expression.degree > 2:
            raise ValueError('A residual exceeds quadratic degree.')
        self.residuals.append(expression)
        self.labels.append(label)

    def wire(self, expression: Polynomial | int) -> Polynomial:
        expression = convert(expression)
        if expression.degree <= 1:
            return expression
        if expression not in self.wire_cache:
            value = expression.evaluate(self.values)
            plus, minus = self.fresh(max(value, 0)), self.fresh(max(-value, 0))
            self.residual(plus * minus, 'canonical signed wire')
            self.residual(plus - minus - expression, 'arithmetic wire')
            self.wire_cache[expression] = plus - minus
        return self.wire_cache[expression]

    def signs(self, expression: Polynomial | int) -> tuple[Polynomial, Polynomial, Polynomial]:
        expression = self.wire(expression)
        if expression not in self.sign_cache:
            value = expression.evaluate(self.values)
            neg, zero, pos = (self.fresh(int(value < 0)),
                              self.fresh(int(value == 0)),
                              self.fresh(int(value > 0)))
            slack = self.fresh(max(abs(value) - 1, 0))
            for bit in (neg, zero, pos):
                self.residual(bit * (bit - 1), 'sign bit')
            self.residual(neg + zero + pos - 1, 'one-hot sign')
            self.residual(expression - (pos - neg) * (slack + 1), 'sign magnitude')
            self.residual(zero * slack, 'zero-sign normalization')
            self.sign_cache[expression] = neg, zero, pos
        return self.sign_cache[expression]

    def equal(self, a: Polynomial | int, b: Polynomial | int) -> Polynomial:
        return self.signs(convert(a) - b)[1]

    def less(self, a: Polynomial | int, b: Polynomial | int) -> Polynomial:
        return self.signs(convert(a) - b)[0]

    def leq(self, a: Polynomial | int, b: Polynomial | int) -> Polynomial:
        return 1 - self.signs(convert(a) - b)[2]

    def conjunction(self, *conditions: Polynomial | int) -> Polynomial:
        result = convert(1)
        for condition in conditions:
            expression = result * condition
            # Boolean output is a single natural variable, uniquely forced.
            if expression.degree <= 1:
                result = expression
            else:
                output = self.fresh(expression.evaluate(self.values))
                self.residual(output - expression, 'Boolean conjunction')
                result = output
        return result

    def require(self, condition: Polynomial | int, label: str) -> None:
        self.residual(1 - convert(condition), label)

    def implication(self, premise: Polynomial | int, conclusion: Polynomial | int,
                    label: str) -> None:
        self.residual(convert(premise) * (1 - convert(conclusion)), label)

    def select(self, bit: Polynomial, yes: Polynomial | int,
               no: Polynomial | int) -> Polynomial:
        return self.wire(convert(no) + bit * (convert(yes) - no))

    def sign_tag(self, expression: Polynomial) -> Polynomial:
        negative, _, positive = self.signs(expression)
        return 1 + positive - negative

    def export(self) -> dict:
        return {
            'format': 'sum-of-squares-quartic-v1',
            'meaning': 'P = sum(Q_i^2); P=0 over natural existential variables',
            'free_parameters': self.inputs,
            'primary_natural_witnesses': self.primary,
            'auxiliary_natural_witnesses': self.auxiliary,
            'residuals': [{'label': label, 'terms': residual.json()}
                          for residual, label in zip(self.residuals, self.labels)],
            'sample_assignment': self.values,
            'statistics': self.statistics(),
        }

    def statistics(self) -> dict:
        failed = [i for i, r in enumerate(self.residuals) if r.evaluate(self.values)]
        natural = self.primary + self.auxiliary
        return {
            'free_parameters': len(self.inputs),
            'primary_natural_witnesses': len(self.primary),
            'auxiliary_natural_witnesses': len(self.auxiliary),
            'total_natural_witnesses': len(natural),
            'quadratic_residuals': len(self.residuals),
            'maximum_residual_degree': max(r.degree for r in self.residuals),
            'quartic_degree_upper_bound': 4,
            'all_sample_witnesses_natural': all(self.values[v] >= 0 for v in natural),
            'failed_sample_residuals': failed,
        }


def compile_certificate(cert: Certificate, require_nonnegative: bool = True) -> Compiler:
    d = len(cert.coefficients) - 1
    cuts_value, tags_value = padded(cert)
    c = Compiler()
    coeff = [c.variable(f'c{i}', value, 'inputs')
             for i, value in enumerate(cert.coefficients)]
    T = c.variable('T', cert.horizon, 'inputs')
    end = T + 1
    tower = [coeff]
    while len(tower[-1]) > 1:
        previous = tower[-1]
        tower.append([sum((comb(r, j) * previous[r]
                           for r in range(j + 1, len(previous))), convert(0))
                      for j in range(len(previous) - 1)])
    cuts, tags, active = [], [], []
    for k in range(d + 1):
        slots = 2 * (d - k) + 1
        b = [convert(0)] + [c.variable(f'b{k}_{j}', cuts_value[k][j], 'primary')
                           for j in range(1, slots)] + [end]
        s = [c.variable(f'tag{k}_{j}', tags_value[k][j], 'primary')
             for j in range(slots)]
        on = [c.less(b[j], b[j + 1]) for j in range(slots)]
        for j in range(slots):
            c.require(c.leq(b[j], b[j + 1]), 'ordered cuts')
            c.require(c.leq(s[j], 2), 'tag domain')
            empty = c.equal(b[j], b[j + 1])
            c.implication(empty, c.equal(b[j], end), 'padding at final endpoint')
            c.implication(empty, c.equal(s[j], 1), 'zero-tag padding')
            if j + 1 < slots:
                c.implication(c.conjunction(on[j], on[j + 1]),
                              1 - c.equal(s[j], s[j + 1]), 'maximal sign runs')
        cuts.append(b)
        tags.append(s)
        active.append(on)
    c.require(c.equal(tags[d][0], c.sign_tag(tower[d][0])), 'constant top difference')

    evaluation_cache: dict[tuple[int, Polynomial], Polynomial] = {}

    def eval_tag(k: int, t: Polynomial) -> Polynomial:
        key = k, t
        if key not in evaluation_cache:
            value = convert(0)
            for coefficient in reversed(tower[k]):
                value = c.wire(value * t) + coefficient
            evaluation_cache[key] = c.sign_tag(value)
        return evaluation_cache[key]

    for k in range(d):
        # Evaluations are cached at candidate endpoints, not recomputed
        # separately at each parent-child intersection.
        for j in range(len(tags[k])):
            a, last = cuts[k][j], cuts[k][j + 1] - 1
            for ell in range(len(tags[k + 1])):
                start, stop = cuts[k + 1][ell], cuts[k + 1][ell + 1]
                choose_a = c.leq(start, a)
                choose_last = c.leq(last, stop)
                lo = c.select(choose_a, a, start)
                hi = c.select(choose_last, last, stop)
                tag_lo = c.select(choose_a, eval_tag(k, a), eval_tag(k, start))
                tag_hi = c.select(choose_last, eval_tag(k, last), eval_tag(k, stop))
                premise = c.conjunction(active[k][j], active[k + 1][ell], c.leq(lo, hi))
                c.implication(premise, c.equal(tag_lo, tags[k][j]), 'left endpoint sign')
                c.implication(premise, c.equal(tag_hi, tags[k][j]), 'right endpoint sign')
    if require_nonnegative:
        for j, tag in enumerate(tags[0]):
            c.implication(active[0][j], 1 - c.equal(tag, 0), 'nonnegative polynomial')
    return c


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', type=int, nargs='+', required=True)
    parser.add_argument('--horizon', type=int, required=True)
    parser.add_argument('--output', default='quartic.json')
    parser.add_argument('--sign-table-only', action='store_true')
    args = parser.parse_args()
    cert = generate(args.coefficients, args.horizon)
    compiler = compile_certificate(cert, not args.sign_table_only)
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(compiler.export(), stream, indent=2)
        stream.write('\n')
    print(json.dumps(compiler.statistics(), indent=2))


if __name__ == '__main__':
    main()
