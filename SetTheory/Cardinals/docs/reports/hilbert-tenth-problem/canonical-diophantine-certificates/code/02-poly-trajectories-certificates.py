#!/usr/bin/env python3
"""Canonical finite-difference sign certificates, using exact integers only.

Coefficient lists are in ascending power order. A certificate describes signs
on the CLOSED integer interval [0, horizon]; runs themselves are half-open.
No floating point, root solver, SMT solver, or horizon-sized trace is used.
This executable checker is not a proof-assistant formalization.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from math import comb
from typing import Sequence
import argparse
import json


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def evaluate(coefficients: Sequence[int], argument: int) -> int:
    result = 0
    for coefficient in reversed(coefficients):
        result = result * argument + coefficient
    return result


def difference(coefficients: Sequence[int]) -> list[int]:
    """Coefficients of p(t+1)-p(t); retain nominal degree, including zeros."""
    return [sum(comb(r, j) * coefficients[r]
                for r in range(j + 1, len(coefficients)))
            for j in range(len(coefficients) - 1)]


def difference_tower(coefficients: Sequence[int]) -> list[list[int]]:
    if not coefficients or any(type(c) is not int for c in coefficients):
        raise ValueError("Supply a nonempty list of integer coefficients.")
    result = [list(coefficients)]
    while len(result[-1]) > 1:
        result.append(difference(result[-1]))
    return result


@dataclass(frozen=True)
class Run:
    start: int
    stop: int
    sign: int


@dataclass
class Certificate:
    coefficients: list[int]
    horizon: int
    levels: list[list[Run]]
    generation_evaluations: int = 0

    def to_dict(self) -> dict:
        return asdict(self)

    @staticmethod
    def from_dict(data: dict) -> 'Certificate':
        return Certificate(list(data['coefficients']), data['horizon'],
                           [[Run(**run) for run in row]
                            for row in data['levels']],
                           data.get('generation_evaluations', 0))


def _merge(runs: list[Run], start: int, stop: int, value: int) -> None:
    if start >= stop:
        return
    if runs and runs[-1].stop == start and runs[-1].sign == value:
        previous = runs.pop()
        runs.append(Run(previous.start, stop, value))
    else:
        runs.append(Run(start, stop, value))


def generate(coefficients: Sequence[int], horizon: int) -> Certificate:
    if type(horizon) is not int or horizon < 0:
        raise ValueError("The horizon must be a nonnegative integer.")
    tower = difference_tower(coefficients)
    degree = len(tower) - 1
    levels: list[list[Run]] = [[] for _ in tower]
    cache: dict[tuple[int, int], int] = {}

    def value(k: int, t: int) -> int:
        key = k, t
        if key not in cache:
            cache[key] = evaluate(tower[k], t)
        return cache[key]

    levels[degree] = [Run(0, horizon + 1, sign(value(degree, 0)))]
    for k in range(degree - 1, -1, -1):
        row: list[Run] = []
        for child in levels[k + 1]:
            # Delta q has a constant sign on [start,stop), so q is
            # monotone there. For decreasing q, search the increasing -q.
            direction = -1 if child.sign < 0 else 1

            def first(strict: bool) -> int:
                lo, hi = child.start, child.stop
                while lo < hi:
                    mid = (lo + hi) // 2
                    v = direction * value(k, mid)
                    if (v > 0 if strict else v >= 0):
                        hi = mid
                    else:
                        lo = mid + 1
                return lo

            nonnegative, positive = first(False), first(True)
            _merge(row, child.start, nonnegative, -direction)
            _merge(row, nonnegative, positive, 0)
            _merge(row, positive, child.stop, direction)
        levels[k] = row
    return Certificate(list(coefficients), horizon, levels, len(cache))


def padded(cert: Certificate) -> tuple[list[list[int]], list[list[int]]]:
    """Return canonical cuts and tags (tag = sign+1), with all fixed slots."""
    degree, end = len(cert.coefficients) - 1, cert.horizon + 1
    cuts, tags = [], []
    for k, runs in enumerate(cert.levels):
        slots = 2 * (degree - k) + 1
        if not runs or len(runs) > slots:
            raise ValueError("Invalid number of sign runs.")
        row_cuts = [run.start for run in runs] + [end]
        row_tags = [run.sign + 1 for run in runs]
        row_cuts += [end] * (slots + 1 - len(row_cuts))
        row_tags += [1] * (slots - len(row_tags))
        cuts.append(row_cuts)
        tags.append(row_tags)
    return cuts, tags


def verify(cert: Certificate, require_nonnegative: bool = False) -> bool:
    """Check local endpoint constraints, NOT a pointwise horizon-sized trace."""
    try:
        if type(cert.horizon) is not int or cert.horizon < 0:
            return False
        tower = difference_tower(cert.coefficients)
        degree = len(tower) - 1
        if len(cert.levels) != len(tower):
            return False
        end = cert.horizon + 1
        for k, row in enumerate(cert.levels):
            if not row or len(row) > 2 * (degree - k) + 1:
                return False
            expected = 0
            previous_sign = None
            for run in row:
                if any(type(v) is not int for v in
                       (run.start, run.stop, run.sign)):
                    return False
                if run.start != expected or not run.start < run.stop <= end:
                    return False
                if run.sign not in (-1, 0, 1) or run.sign == previous_sign:
                    return False
                expected, previous_sign = run.stop, run.sign
            if expected != end:
                return False
        if cert.levels[degree] != [Run(0, end, sign(tower[degree][0]))]:
            return False
        cache: dict[tuple[int, int], int] = {}

        def actual_sign(k: int, t: int) -> int:
            if (k, t) not in cache:
                cache[k, t] = sign(evaluate(tower[k], t))
            return cache[k, t]

        for k in range(degree - 1, -1, -1):
            for parent in cert.levels[k]:
                for child in cert.levels[k + 1]:
                    lo = max(parent.start, child.start)
                    # The child STOP, not stop-1, is intentional:
                    # Delta q on [c,e) makes q monotone on [c,e].
                    hi = min(parent.stop - 1, child.stop)
                    if lo <= hi and (actual_sign(k, lo) != parent.sign or
                                     actual_sign(k, hi) != parent.sign):
                        return False
        return not require_nonnegative or all(run.sign >= 0 for run in cert.levels[0])
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False


def brute_runs(coefficients: Sequence[int], horizon: int) -> list[Run]:
    result: list[Run] = []
    for t in range(horizon + 1):
        _merge(result, t, t + 1, sign(evaluate(coefficients, t)))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', type=int, nargs='+', required=True,
                        help='Ascending power order, e.g. 8 -6 1')
    parser.add_argument('--horizon', type=int, required=True)
    parser.add_argument('--output', default=None)
    args = parser.parse_args()
    certificate = generate(args.coefficients, args.horizon)
    data = certificate.to_dict()
    data['verified'] = verify(certificate)
    data['nonnegative'] = verify(certificate, require_nonnegative=True)
    text = json.dumps(data, indent=2)
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as stream:
            stream.write(text + '\n')
    else:
        print(text)


if __name__ == '__main__':
    main()
