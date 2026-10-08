"""Twist-block reduced Khovanov homology over F_2, quantum grading forgotten.

This is an independent, opt-in backend, not a replacement for fastunknot's
scanner.  Its input parameter is the number of signed braid runs, not braid
index, crossing number, or diagrammatic twist number. See synthesis/research_updates.tex and research report 11.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from math import prod, isfinite, log2
from time import monotonic
from typing import Iterable, Sequence


class ResourceLimit(RuntimeError):
    """A budget was exhausted; this exception is never a knot verdict."""


@dataclass(frozen=True)
class Run:
    generator: int  # 1-based, unsigned Artin generator
    exponent: int   # signed and nonzero


@dataclass
class Budget:
    max_states: int = 250_000
    max_basis: int = 1_000_000
    max_matrix_bits: int = 1_000_000_000
    max_xors: int = 20_000_000
    seconds: float | None = None

    def __post_init__(self):
        for name in ('max_states', 'max_basis', 'max_matrix_bits', 'max_xors'):
            value = getattr(self, name)
            if type(value) is not int or value < 0:
                raise ValueError(f'{name} must be a nonnegative integer')
        if self.seconds is not None and (not isinstance(self.seconds, (int, float))
                                         or not isfinite(self.seconds) or self.seconds < 0):
            raise ValueError('seconds must be a finite nonnegative number')


class _Meter:
    def __init__(self, budget: Budget):
        self.budget = budget
        self.deadline = None if budget.seconds is None else monotonic() + budget.seconds
        self.xors = 0

    def check(self):
        if self.deadline is not None and monotonic() >= self.deadline:
            raise ResourceLimit('time budget exhausted')

    def xor(self):
        self.xors += 1
        if self.xors > self.budget.max_xors:
            raise ResourceLimit('rank/d-squared XOR budget exhausted')
        if self.xors & 1023 == 0:
            self.check()


def validate_runs(strands: int, runs: Iterable[Run]) -> tuple[Run, ...]:
    if type(strands) is not int or strands < 1:
        raise ValueError('strands must be a positive integer')
    runs = tuple(runs)
    for r in runs:
        if not isinstance(r, Run) or type(r.generator) is not int or type(r.exponent) is not int:
            raise ValueError('each run must have integer generator and exponent')
        if not 1 <= r.generator < strands or r.exponent == 0:
            raise ValueError('invalid generator or zero exponent')
    return runs


def runs_from_word(strands: int, word: Iterable[int], *, cancel: bool = False) -> tuple[Run, ...]:
    """Group equal signed letters. Optional adjacent inverse cancellation.

    With cancel=False no isotopy preprocessing is hidden in benchmarks.
    """
    validate_runs(strands, ())
    out: list[Run] = []
    for letter in word:
        if type(letter) is not int or not 0 < abs(letter) < strands:
            raise ValueError('braid letters must be nonzero integers of absolute value < strands')
        g, s = abs(letter), 1 if letter > 0 else -1
        if out and out[-1].generator == g and (cancel or out[-1].exponent * s > 0):
            e = out[-1].exponent + s
            out.pop()
            if e:
                out.append(Run(g, e))
        else:
            out.append(Run(g, s))
    return validate_runs(strands, out)


def components(strands: int, runs: Iterable[Run]) -> int:
    runs = validate_runs(strands, runs)
    # Track only touched positions. A huge encoded strand count must not allocate
    # an equally huge permutation before a resource check can take place.
    p: dict[int, int] = {}
    for r in runs:
        if abs(r.exponent) % 2:
            i = r.generator - 1
            p[i], p[i + 1] = p.get(i + 1, i + 1), p.get(i, i)
    seen: set[int] = set()
    result = strands - len(p)
    for i in p:
        if i in seen:
            continue
        result += 1
        while i not in seen:
            seen.add(i)
            i = p[i]
    return result


@dataclass(frozen=True)
class Geometry:
    circles: tuple[frozenset[int], ...]  # marked circle is always first
    owner: tuple[int, ...]

    @property
    def dimension(self) -> int:
        return 1 << (len(self.circles) - 1)


def _geometry(strands: int, runs: Sequence[Run], support: int) -> Geometry:
    """Close the I/E Temperley--Lieb state on a (t+1)-by-b vertex grid."""
    t = len(runs)
    parent = list(range((t + 1) * strands))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def join(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[b] = a

    for k, r in enumerate(runs):
        i = r.generator - 1
        top, bot = k * strands, (k + 1) * strands
        e = bool(support & (1 << k))
        for j in range(strands):
            if not e or j not in (i, i + 1):
                join(top + j, bot + j)
        if e:
            join(top + i, top + i + 1)
            join(bot + i, bot + i + 1)
    for j in range(strands):
        join(j, t * strands + j)
    groups: dict[int, set[int]] = defaultdict(set)
    for x in range(len(parent)):
        groups[find(x)].add(x)
    circles = tuple(sorted((frozenset(s) for s in groups.values()), key=min))
    owner = [0] * len(parent)
    for j, c in enumerate(circles):
        for x in c:
            owner[x] = j
    return Geometry(circles, tuple(owner))


def _saddle_map(source: Geometry, target: Geometry) -> tuple[tuple[int, ...], ...]:
    """Columns of the reduced multiplication/comultiplication map.

    Labels are monomials. Bit j records X on circle j+1. Circle zero is
    constrained to X. Equal output labels cancel over F_2.
    """
    relation = [{target.owner[v] for v in c} for c in source.circles]
    nc, nd = len(source.circles), len(target.circles)
    if abs(nc - nd) != 1:
        raise ArithmeticError('a classical saddle must merge or split one circle')
    images = []
    for label in range(source.dimension):
        xmask = (label << 1) | 1
        output: set[int] = set()
        if nc == nd + 1:  # multiplication
            counts = [0] * nd
            for j, targets in enumerate(relation):
                if len(targets) != 1:
                    raise ArithmeticError('invalid merge relation')
                if xmask & (1 << j):
                    counts[next(iter(targets))] += 1
            if max(counts, default=0) < 2:
                y = sum((bool(c) << j) for j, c in enumerate(counts))
                if not y & 1:
                    raise ArithmeticError('marked subcomplex was not preserved')
                output.add(y >> 1)
        else:  # comultiplication
            split = [j for j, targets in enumerate(relation) if len(targets) == 2]
            if len(split) != 1:
                raise ArithmeticError('invalid split relation')
            j = split[0]
            a, b = sorted(relation[j])
            y = 0
            for k, targets in enumerate(relation):
                if k != j and xmask & (1 << k):
                    if len(targets) != 1:
                        raise ArithmeticError('invalid unaffected circle')
                    y |= 1 << next(iter(targets))
            masks = [y | (1 << a) | (1 << b)] if xmask & (1 << j) else [y | (1 << a), y | (1 << b)]
            for z in masks:
                if not z & 1:
                    raise ArithmeticError('marked subcomplex was not preserved')
                q = z >> 1
                if q in output:
                    output.remove(q)
                else:
                    output.add(q)
        images.append(tuple(sorted(output)))
    return tuple(images)


def _dot_map(geometry: Geometry, a: int, b: int) -> tuple[tuple[int, ...], ...]:
    """The internal twist differential: X on the top arc plus X on bottom."""
    ca, cb = geometry.owner[a], geometry.owner[b]
    if ca == cb:
        return ((),) * geometry.dimension
    images = []
    for label in range(geometry.dimension):
        images.append(tuple(sorted(label | (1 << (c - 1)) for c in (ca, cb)
                                   if c != 0 and not label & (1 << (c - 1)))))
    return tuple(images)


@dataclass
class Complex:
    dimensions: dict[int, int]
    columns: dict[int, list[int]]
    stats: dict[str, int]


def build_complex(strands: int, runs: Iterable[Run], *, budget: Budget | None = None,
                  meter: _Meter | None = None) -> Complex:
    """Build the macro complex. Does not infer or require that the closure is a knot."""
    runs = validate_runs(strands, runs)
    meter = meter or _Meter(budget or Budget())
    cap = meter.budget
    t = len(runs)
    states_count = 1
    if states_count > cap.max_states:
        raise ResourceLimit('macro state limit exceeded')
    for run in runs:
        meter.check()
        # Reject before constructing or formatting a huge product. This also
        # handles binary-encoded exponents beyond Python's decimal digit cap.
        factor = abs(run.exponent) + 1
        if factor > cap.max_states // states_count:
            raise ResourceLimit('macro state limit exceeded')
        states_count *= factor
    meter.check()
    geometry: dict[int, Geometry] = {}
    state_info: dict[tuple[int, ...], tuple[int, int, int]] = {}
    dims: dict[int, int] = defaultdict(int)
    total_basis = 0
    ranges = [range(abs(r.exponent) + 1) for r in runs]
    for state in product(*ranges):
        meter.check()
        support = sum((1 << j) for j, k in enumerate(state) if k)
        if support not in geometry:
            # A cheap guard before allocating a large grid in malformed/huge link inputs.
            if (t + 1) * strands > 4 * max(1, cap.max_basis):
                raise ResourceLimit('topology grid exceeds budget-derived limit')
            geometry[support] = _geometry(strands, runs, support)
        g = geometry[support]
        h = sum(k if r.exponent > 0 else -k for k, r in zip(state, runs))
        state_info[state] = (h, dims[h], support)
        dims[h] += g.dimension
        total_basis += g.dimension
        if total_basis > cap.max_basis:
            raise ResourceLimit(f'basis count exceeds {cap.max_basis}')
    bits = sum(d * dims.get(h + 1, 0) for h, d in dims.items())
    if bits > cap.max_matrix_bits:
        raise ResourceLimit(f'dense matrix-bit upper bound {bits} exceeds {cap.max_matrix_bits}')
    columns = {h: [0] * d for h, d in dims.items()}
    maps: dict[tuple[int, int, str], tuple[tuple[int, ...], ...]] = {}
    nnz = 0
    for state, (h, offset, support) in state_info.items():
        meter.check()
        source = geometry[support]
        for j, (k, r) in enumerate(zip(state, runs)):
            if r.exponent > 0:
                if k == r.exponent:
                    continue
                kk = k + 1
            else:
                if k == 0:
                    continue
                kk = k - 1
            target_state = state[:j] + (kk,) + state[j + 1:]
            hh, target_offset, target_support = state_info[target_state]
            if hh != h + 1:
                raise ArithmeticError('differential has incorrect homological degree')
            kind = 'saddle' if not k or not kk else 'dot'
            key = (support, j, kind)
            if key not in maps:
                if kind == 'saddle':
                    maps[key] = _saddle_map(source, geometry[target_support])
                else:
                    i = r.generator - 1
                    maps[key] = _dot_map(source, j * strands + i, (j + 1) * strands + i)
            for label, targets in enumerate(maps[key]):
                for q in targets:
                    columns[h][offset + label] ^= 1 << (target_offset + q)
                    nnz += 1
    return Complex(dict(dims), columns, {
        'crossings': sum(abs(r.exponent) for r in runs), 'runs': t,
        'macro_states': states_count, 'geometry_states': len(geometry),
        'compiled_maps': len(maps), 'basis': total_basis,
        'differential_entries': nnz, 'matrix_bit_upper_bound': bits,
        'peak_chain_dimension': max(dims.values(), default=0),
        'rank_xor_bit_upper_bound': sum(d * dims.get(h + 1, 0) * min(d, dims.get(h + 1, 0))
                                        for h, d in dims.items()),
    })


def _rank(columns: Iterable[int], meter: _Meter) -> int:
    pivots: dict[int, int] = {}
    for column in columns:
        meter.check()
        while column:
            p = column.bit_length() - 1
            if p not in pivots:
                pivots[p] = column
                break
            column ^= pivots[p]
            meter.xor()
    return len(pivots)


def verify_d_squared(complex_: Complex, meter: _Meter | None = None) -> None:
    meter = meter or _Meter(Budget())
    for h, columns in complex_.columns.items():
        following = complex_.columns.get(h + 1, [])
        for column in columns:
            meter.check()
            image = 0
            while column:
                low = column & -column
                j = low.bit_length() - 1
                image ^= following[j]
                column ^= low
                meter.xor()
            if image:
                raise ArithmeticError(f'd^2 != 0 in degree {h}')


def homology(strands: int, runs: Iterable[Run], *, budget: Budget | None = None,
             check_d2: bool = False) -> dict:
    start = monotonic()
    runs = validate_runs(strands, runs)
    meter = _Meter(budget or Budget())
    c = build_complex(strands, runs, meter=meter)
    if check_d2:
        verify_d_squared(c, meter)
    ranks = {h: _rank(cols, meter) for h, cols in c.columns.items()}
    by_degree = {h: d - ranks.get(h - 1, 0) - ranks[h] for h, d in c.dimensions.items()}
    if any(x < 0 for x in by_degree.values()):
        raise ArithmeticError('negative homology dimension')
    by_degree = {h: d for h, d in sorted(by_degree.items()) if d}
    return {'reduced_rank': sum(by_degree.values()), 'by_degree': by_degree,
            'chain_dimensions': dict(sorted(c.dimensions.items())),
            'boundary_ranks': dict(sorted(ranks.items())),
            'components': components(strands, runs),
            'stats': {**c.stats, 'elimination_and_check_xors': meter.xors},
            'seconds': monotonic() - start, 'd_squared_checked': check_d2}


def recognize(strands: int, runs: Iterable[Run], *, budget: Budget | None = None,
              check_d2: bool = False) -> dict:
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError('unknot recognition requires a one-component braid closure')
    try:
        result = homology(strands, runs, budget=budget, check_d2=check_d2)
    except (ResourceLimit, MemoryError) as exc:
        return {'status': 'UNKNOWN', 'method': 'twist-khovanov-F2',
                'reason': str(exc) or 'memory allocation failed',
                'unrestricted_quasipolynomial_guarantee': False}
    return {'status': 'UNKNOT' if result['reduced_rank'] == 1 else 'KNOTTED',
            'method': 'twist-khovanov-F2', 'homology': result,
            'unrestricted_quasipolynomial_guarantee': False}


def size_estimate(strands: int, runs: Iterable[Run], *, max_supports: int = 65_536,
                  max_grid_vertices: int = 1_000_000) -> dict:
    """Exact basis count by support subsets, or a cheap upper bound.

    Does not enumerate the product of run lengths. A declared limit on the
    number of supports or grid vertices turns off the exact part only.
    Bounds are on algebraic dimensions, not the Python process's peak memory.
    """
    runs = validate_runs(strands, runs)
    if type(max_supports) is not int or max_supports < 0:
        raise ValueError('max_supports must be a nonnegative integer')
    if type(max_grid_vertices) is not int or max_grid_vertices < 0:
        raise ValueError('max_grid_vertices must be a nonnegative integer')
    t = len(runs)
    ms = [abs(r.exponent) for r in runs]
    # Keep the upper bound in log form for huge, binary-encoded strand counts.
    log_upper = strands - 1 + sum(log2(1 + 2*m) for m in ms)
    result = {'strands': strands, 'runs': t, 'crossings': sum(ms),
              'components': components(strands, runs),
              'macro_states': prod(m+1 for m in ms),
              'log2_basis_upper_bound': log_upper,
              'exact_basis': None, 'supports_evaluated': 0}
    if t >= max_supports.bit_length() or (t+1)*strands > max_grid_vertices:
        return result
    total = 0
    histogram: dict[int, int] = defaultdict(int)
    for support in range(1 << t):
        g = _geometry(strands, runs, support)
        weight = prod(ms[j] for j in range(t) if support & (1 << j))
        total += g.dimension * weight
        histogram[len(g.circles)] += 1
    result.update(exact_basis=total, supports_evaluated=1 << t,
                  support_circle_histogram=dict(sorted(histogram.items())))
    return result

