#!/usr/bin/env python3
"""Exact regression certificates for prime-cyclic Bohr boundary obstructions.

Python 3.10+, standard library only. No floating point is used in a test.
The manuscript proves the infinite families; these checks are not Lean proofs.
Run: python3 code/verify.py --output verification.json
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, gcd, prod
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def ceil(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def floor(x: F) -> int:
    return x.numerator // x.denominator


def tnorm(x: F) -> F:
    x %= 1
    return min(x, 1 - x)


def trial_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def lucas_lehmer(exponent: int) -> int:
    """Return a Mersenne prime, checking its prime exponent and LL residue."""
    require(trial_prime(exponent), 'Lucas-Lehmer exponent is not prime')
    if exponent == 2:
        return 3
    p = (1 << exponent) - 1
    residue = 4
    for _ in range(exponent - 2):
        residue = (residue * residue - 2) % p
    require(residue == 0, f'Mersenne number of exponent {exponent} failed')
    return p


@dataclass(frozen=True)
class Model:
    rank: int
    T: int

    def __post_init__(self) -> None:
        require(self.rank >= 2, 'rank must be at least two')
        require(self.T % self.D == 1 % self.D, 'T congruence failed')
        require(self.T >= 2 * self.s * self.D + 4, 'T size failed')
        require(all(gcd(q, z) == 1 for q, z in combinations(self.q, 2)),
                'CRT factors are not pairwise coprime')

    @property
    def s(self) -> int:
        return self.rank - 1

    @property
    def D(self) -> int:
        return factorial(self.s)

    @property
    def q(self) -> tuple[int, ...]:
        return tuple(self.T + i * self.D for i in range(1, self.s + 1))

    @property
    def A(self) -> int:
        return prod(self.q)

    @property
    def frequencies(self) -> tuple[int, ...]:
        return (self.A,) + tuple(self.A + self.A // q for q in self.q)

    @property
    def rho(self) -> F:
        return F(1, 2 * self.T)

    @property
    def M(self) -> int:
        return (1 << self.rank) - 1

    def crt(self, residues: tuple[int, ...]) -> int:
        require(len(residues) == self.s, 'CRT residue length mismatch')
        x = sum(y * (self.A // q) * pow(self.A // q, -1, q)
                for y, q in zip(residues, self.q)) % self.A
        require(all(x % q == y % q for q, y in zip(self.q, residues)),
                'CRT reconstruction failed')
        return x

    def intervals(self, rho: F | None = None) -> list[tuple[F, F]]:
        rho = self.rho if rho is None else rho
        L = tuple((1 - rho * q) / (q + 1) for q in self.q)
        U = tuple(rho * q / (q + 1) for q in self.q)
        arcs = [(-U[0] / self.A, U[0] / self.A)]
        for mask in range(1, 1 << self.s):
            present = [i for i in range(self.s) if mask & (1 << i)]
            absent = [i for i in range(self.s) if not mask & (1 << i)]
            lo = max(L[i] for i in present)
            hi = min((U[i] for i in absent), default=rho)
            require(lo < hi, 'empty spike interval')
            x = self.crt(tuple(-int(i in present) for i in range(self.s)))
            left, right = (x + lo) / self.A, (x + hi) / self.A
            arcs += [(left, right), (-right, -left)]
        require(len(arcs) == self.M, 'component count failed')
        return arcs

    def mass_formula(self, rho: F | None = None) -> F:
        rho = self.rho if rho is None else rho
        weighted_sum = sum((F(1 << (self.s - i), self.T + i * self.D + 1)
                            for i in range(1, self.s + 1)), F(0))
        return (2 * rho * self.M - 2 * (2 * rho + 1) * weighted_sum) / self.A

    def F_budget(self) -> F:
        return 1 + 2 * self.D * sum(
            (F(i * (1 << (self.s - i)), self.T + i * self.D + 1)
             for i in range(1, self.s + 1)), F(0))

    def limiting_ratio(self) -> F:
        return F(self.M, 2) / ((1 + F(1, self.q[0])) * self.F_budget())

    def in_bohr(self, t: F, rho: F | None = None) -> bool:
        rho = self.rho if rho is None else rho
        return all(tnorm(a * t) <= rho for a in self.frequencies)


def geometry(model: Model, rho: F | None = None) -> dict:
    rho = model.rho if rho is None else rho
    arcs = model.intervals(rho)
    lengths = [hi - lo for lo, hi in arcs]
    require(sum(lengths, F(0)) == model.mass_formula(rho), 'mass formula failed')
    normalized = sorted((lo % 1, hi - lo) for lo, hi in arcs)
    gaps = []
    for j, (lo, length) in enumerate(normalized):
        next_lo = normalized[(j + 1) % len(normalized)][0] + int(j == len(normalized)-1)
        gap = next_lo - lo - length
        require(gap > 0, 'arcs overlap')
        gaps.append(gap)
    required_min = F(1, 8 * model.A * model.T**2)
    require(min(lengths) >= required_min, 'robust minimum arc length failed')
    require(min(gaps) >= F(1 - 2 * rho, model.A), 'base-cell gap failed')
    for lo, hi in arcs:
        for t in (lo, (lo + hi) / 2, hi):
            require(model.in_bohr(t, rho), 'described interval point outside Bohr set')
    return {'arcs': len(arcs), 'mass': str(sum(lengths, F(0))),
            'minimum_arc_length': str(min(lengths)), 'minimum_gap': str(min(gaps))}


def exact_grid(model: Model, p: int) -> dict:
    arcs = model.intervals()
    require(p > 8 * model.A * model.T**2, 'grid below sufficient threshold')
    lengths = [hi - lo for lo, hi in arcs]
    count = sum(floor(p * hi) - ceil(p * lo) + 1 for lo, hi in arcs)
    mu = model.mass_formula()
    require(all(p * length > 2 for length in lengths), 'too few points per component')
    require(abs(count - p * mu) <= model.M, 'grid discrepancy failed')
    require(p > 2 * max(model.frequencies), 'frequencies may wrap')
    eta = F(max(model.frequencies), 1) / (model.rho * p)
    ratio = F(model.M, count) / eta
    predicted = model.limiting_ratio()
    relative_error_bound = F(model.M, p) / mu
    require(predicted / (1 + relative_error_bound) <= ratio,
            'finite lower comparison failed')
    require(ratio <= predicted / (1 - relative_error_bound),
            'finite upper comparison failed')
    return {'prime': str(p), 'cardinality': str(count), 'boundary': model.M,
            'relative_step': str(eta), 'ratio': str(ratio),
            'ratio_decimal_for_display_only': f'{float(ratio):.10f}',
            'limiting_ratio': str(predicted),
            'limiting_ratio_decimal_for_display_only': f'{float(predicted):.10f}'}


def irredundancy(model: Model) -> int:
    count = 0
    for i in range(model.s):
        residues = tuple(2 * int(j == i) for j in range(model.s))
        t = F(model.crt(residues), model.A)
        tests = [tnorm(a*t) <= model.rho for a in model.frequencies]
        require(tests == [j != i + 1 for j in range(model.rank)],
                'non-base irredundancy witness failed')
        require(all(tnorm(a*t) < model.rho for j, a in enumerate(model.frequencies) if j != i+1),
                'retained irredundancy constraint is not strict')
        require(tnorm(model.frequencies[i+1]*t) > model.rho, 'deleted constraint not strictly violated')
        count += 1
    x = model.crt((-1,) * model.s)
    u = model.rho + (1-model.rho) / (2 * (model.q[-1]+1))
    t = (x + u) / model.A
    tests = [tnorm(a*t) <= model.rho for a in model.frequencies]
    require(tests == [False] + [True] * model.s, 'base irredundancy witness failed')
    require(all(tnorm(a*t) < model.rho for a in model.frequencies[1:]),
            'retained base-deletion constraint is not strict')
    require(tnorm(model.frequencies[0]*t) > model.rho, 'base constraint not strictly violated')
    return count + 1


def brute_grid(model: Model, p: int) -> dict:
    require(trial_prime(p), 'brute modulus not prime')
    denominator = 2 * model.T
    fs = model.frequencies
    B = bytearray(p)
    for x in range(p):
        B[x] = all(denominator * min((a*x) % p, (-a*x) % p) <= p for a in fs)
    count = sum(B)
    boundary = sum(bool(B[x]) and not B[(x+1) % p] for x in range(p))
    prediction = exact_grid(model, p)
    require(count == int(prediction['cardinality']), 'brute cardinality mismatch')
    require(boundary == model.M, 'brute boundary mismatch')
    return {'rank': model.rank, 'T': model.T, 'prime': p,
            'cardinality': count, 'boundary': boundary,
            'points_exhaustively_checked': p}


def small_cell_classification(model: Model) -> dict:
    """Independently intersect all constraints in every a0-cell, including empties."""
    require(model.A <= 1000, 'cell exhaustion limited to small product')
    rho = model.rho
    intervals = []
    for x in range(model.A):
        lo, hi = -rho, rho
        for q in model.q:
            y = x % q
            if 2*y > q:
                y -= q
            # On each cell the centered residue can wrap only near 1/2;
            # check the three integer representatives independently.
            pieces = []
            a = 1 + F(1, q)
            for shift in (-1, 0, 1):
                lower = max(lo, (-rho - F(y, q) + shift) / a)
                upper = min(hi, (rho - F(y, q) + shift) / a)
                if lower <= upper:
                    pieces.append((lower, upper))
            if not pieces:
                lo, hi = F(1), F(0)
                break
            require(len(pieces) == 1, 'unexpected split in narrow cell')
            lo, hi = pieces[0]
        if lo <= hi:
            require(lo < hi, 'unexpected singleton')
            intervals.append(((x + lo) / model.A, (x + hi) / model.A))
    require(len(intervals) == model.M, 'all-cell count mismatch')
    require(sum((b-a for a,b in intervals), F(0)) == model.mass_formula(),
            'all-cell mass mismatch')
    return {'rank': model.rank, 'T': model.T, 'cells_exhausted': model.A,
            'nonempty_cells': len(intervals)}


def escape_regression() -> dict:
    """Exact independent finite checks of the attributed escape-tube upper bound."""
    tests = 0
    positive = 0
    for n in range(3, 32):
        for rank in range(1, 3):
            for fs in combinations(range(1, min(n//2, 5) + 1), rank):
                for rho in (F(1, 4), F(1, 5), F(1, 7)):
                    B = {x for x in range(n) if all(tnorm(F(a*x, n)) <= rho for a in fs)}
                    large = {x for x in range(n) if all(tnorm(F(a*x, n)) <= F(3,2)*rho for a in fs)}
                    require(len(large) <= 3**rank * len(B), 'packing bound failed')
                    for d in range(1, n):
                        eta = max(tnorm(F(a*d, n))/rho for a in fs)
                        if not 0 < eta <= F(1,2):
                            continue
                        m = floor(1/(2*eta))
                        boundary = len({x for x in B if (x+d) % n not in B})
                        require(2*m*boundary <= len(large)-len(B), 'escape bound failed')
                        tests += 1
                        positive += int(boundary > 0)
    return {'instances': tests, 'positive_boundary_instances': positive}



def rank_one_checks() -> dict:
    cases = 0
    for q in range(4, 90):
        for rho in (F(1,4), F(1,5), F(1,7), F(3,16)):
            B = {x for x in range(q) if tnorm(F(x,q)) <= rho}
            for k in range(1, q//2 + 1):
                eta = F(k,q) / rho
                if eta > 1:
                    continue
                boundary = sum((x+k) % q not in B for x in B)
                require(boundary == k, 'rank-one exact boundary failed')
                ratio = F(boundary,len(B)) / eta
                require(ratio <= 1/(2-eta), 'rank-one upper bound failed')
                cases += 1
    return {'instances': cases}


def probability_checks() -> dict:
    cases = 0
    for n in range(2, 9):
        for mask in range(1, 1 << n):
            B = [x for x in range(n) if mask & (1 << x)]
            mu = tuple(F(int(x in B),len(B)) for x in range(n))
            for d in range(n):
                shifted = tuple(mu[(x-d) % n] for x in range(n))
                tv = sum((abs(a-b) for a,b in zip(mu,shifted)),F(0))/2
                boundary = sum((x+d) % n not in B for x in B)
                require(tv == F(boundary,len(B)), 'TV boundary identity failed')
                # Three rational probability measures, not an optimization algorithm.
                candidates = [tuple(F(1,n) for _ in range(n)),
                              tuple(F(x+1,n*(n+1)//2) for x in range(n)),
                              tuple((a+b)/2 for a,b in zip(mu,shifted))]
                for nu in candidates:
                    error = sum((abs(a-b) for a,b in zip(nu,mu)),F(0))/2
                    translated = tuple(nu[(x-d) % n] for x in range(n))
                    instability = sum((abs(a-b) for a,b in zip(nu,translated)),F(0))/2
                    require(instability + 2*error >= tv, 'probability tradeoff failed')
                    cases += 1
    return {'measure_shift_instances': cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    parser.add_argument('--certificates', type=Path, default=Path('arc_certificates.json'))
    args = parser.parse_args()
    mersenne = {e: lucas_lehmer(e) for e in (31, 61, 127, 521)}
    models = [(2, 10, 31), (3, 17, 31), (4, 43, 61),
              (5, 217, 127), (6, 1321, 127),
              (3, 10001, 127), (4, 60001, 127),
              (5, 240001, 521), (6, 1200001, 521), (8, 50400001, 521)]
    records = []
    certificates = []
    for rank, T, exponent in models:
        model = Model(rank, T)
        row = {'rank': rank, 'T': T, 'q': model.q, 'A': str(model.A),
               'frequencies': [str(a) for a in model.frequencies],
               'rho': str(model.rho), 'M': model.M}
        row['geometry'] = geometry(model)
        h = F(1, 16*T*T)
        row['radius_window_checks'] = [geometry(model, model.rho + sign*h) for sign in (-1, 1)]
        require(model.mass_formula() == model.F_budget() / (model.A*T), 'special mass formula failed')
        H = (1 << rank) - rank - 1
        require(1 <= model.F_budget() <= 1 + F(2*model.D*H, T), 'budget inequality failed')
        require(model.limiting_ratio() < F(model.M, 2), 'limiting family upper endpoint failed')
        row['irredundancy_witnesses'] = irredundancy(model)
        row['grid'] = exact_grid(model, mersenne[exponent])
        row['mersenne_exponent'] = exponent
        records.append(row)
        p = mersenne[exponent]
        certificates.append({'rank':rank, 'T':T, 'prime':str(p),
            'arcs':[{'left':str(lo), 'right':str(hi),
                     'grid_count':str(floor(p*hi)-ceil(p*lo)+1)}
                    for lo,hi in model.intervals()]})
    exhaustive = [brute_grid(Model(2,10), 10007), brute_grid(Model(3,17), 1000003)]
    cells = [small_cell_classification(Model(2, T)) for T in (6, 10, 30)]
    cells += [small_cell_classification(Model(3, T)) for T in (13, 17, 25)]
    report = {'status': 'all exact checks passed',
              'arithmetic': 'Python integers and fractions; display-only decimals are labeled',
              'formal_status': 'not a proof-assistant certificate',
              'mersenne_primality_checks': list(mersenne),
              'models': records, 'exhaustive_prime_grids': exhaustive,
              'exhaustive_cells': cells, 'escape_regression': escape_regression(),
              'rank_one_regression': rank_one_checks(),
              'probability_regression': probability_checks()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    args.certificates.parent.mkdir(parents=True, exist_ok=True)
    args.certificates.write_text(json.dumps(certificates, indent=2)+'\n', encoding='utf-8')
    print(report['status'])
    print('Exhaustively checked prime-grid points:', sum(r['points_exhaustively_checked'] for r in exhaustive))
    print('Exhaustively classified cells:', sum(r['cells_exhausted'] for r in cells))
    print('Escape instances:', report['escape_regression'])
    for row in records:
        print('rank', row['rank'], 'T', row['T'], 'components', row['M'],
              'ratio', row['grid']['ratio_decimal_for_display_only'],
              'target', F(row['M'], 2))
    print('Rank-one instances:', report['rank_one_regression'])
    print('Probability instances:', report['probability_regression'])
    print('Wrote', args.output, 'and', args.certificates)


if __name__ == '__main__':
    main()
