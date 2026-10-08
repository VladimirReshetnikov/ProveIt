"""Degree-streamed exact twist-macro homology over F_2.

This is an additive backend for the same complex as ``twist.core``.  It
changes storage and enumeration, not the underlying topological algorithm.
Two adjacent state indexes suffice.  Columns go straight into elimination;
optional d-squared checking additionally retains two adjacent matrices.

Budgets bound mathematical storage units, not Python allocator/RSS bytes.
In particular ``max_live_matrix_bits`` bounds a conservative live bit-payload
envelope (including four temporary row vectors), and ``max_live_columns``
bounds retained matrix/pivot references plus temporary vectors.  Geometry
and compact map caches have independent, explicit caps.  ResourceLimit is
never an unknot verdict.  See STREAMING_NOTES.md for all counting conventions.
"""
from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from math import isfinite
from time import monotonic
from typing import Iterable, Iterator

from .core import Geometry, ResourceLimit, Run, _geometry, components, validate_runs


@dataclass
class StreamBudget:
    """Structural limits; zero cache capacity disables that cache."""

    max_states: int = 250_000
    max_basis: int = 1_000_000
    max_live_states: int = 250_000
    max_layer_basis: int = 1_000_000
    max_live_matrix_bits: int = 1_000_000_000
    max_live_columns: int = 2_000_000
    max_grid_vertices: int = 1_000_000
    max_geometry_cache_entries: int = 128
    max_geometry_cache_vertices: int = 1_000_000
    max_map_cache_entries: int = 1_024
    max_map_cache_slots: int = 100_000
    max_active_map_slots: int = 1_000_000
    max_xors: int = 20_000_000
    seconds: float | None = None

    def __post_init__(self):
        for name in self.__dataclass_fields__:
            if name == 'seconds':
                continue
            value = getattr(self, name)
            if type(value) is not int or value < 0:
                raise ValueError(f'{name} must be a nonnegative integer')
        if self.seconds is not None and (
            type(self.seconds) not in (int, float)
            or not isfinite(self.seconds) or self.seconds < 0
        ):
            raise ValueError('seconds must be a finite nonnegative number')


class _Meter:
    def __init__(self, budget: StreamBudget):
        self.budget = budget
        self.deadline = None if budget.seconds is None else monotonic() + budget.seconds
        self.xors = 0
        self.live_states = 0
        self.live_layers = 0
        self.materialized_bits = 0
        self.materialized_columns = 0
        self.pivots = 0
        self.pivot_bits = 0
        self.rank_width = 0
        self.stats: dict[str, int] = {
            'enumerated_macro_states': 0,
            'basis': 0,
            'peak_live_states': 0,
            'peak_live_layers': 0,
            'peak_chain_dimension': 0,
            'geometry_builds': 0,
            'geometry_cache_hits': 0,
            'geometry_cache_entries_peak': 0,
            'geometry_cache_vertices_peak': 0,
            'map_compilations': 0,
            'map_cache_hits': 0,
            'map_cache_entries_peak': 0,
            'map_cache_slots_peak': 0,
            'active_map_slots_peak': 0,
            'active_edges_peak': 0,
            'differential_entries': 0,
            'matrix_bit_upper_bound': 0,
            'rank_xor_bit_upper_bound': 0,
            'peak_pivot_count': 0,
            'peak_pivot_bit_length_sum': 0,
            'peak_live_matrix_bit_upper_bound': 0,
            'peak_live_columns': 0,
            'peak_materialized_matrix_columns': 0,
            'peak_materialized_matrix_bit_upper_bound': 0,
        }

    def peak(self, name: str, value: int):
        self.stats[name] = max(self.stats[name], value)

    def check(self):
        if self.deadline is not None and monotonic() >= self.deadline:
            raise ResourceLimit('time budget exhausted')

    def xor(self):
        self.xors += 1
        if self.xors > self.budget.max_xors:
            raise ResourceLimit('rank/d-squared XOR budget exhausted')
        if self.xors & 1023 == 0:
            self.check()

    def algebra_check(self, *, extra_bits: int | None = None,
                      extra_columns: int = 4):
        # Four vectors cover the yielded generator value, an evolving reduced
        # column, a shifted unit vector, and an allocated XOR result.  Several
        # of these are usually absent or aliases, so this is conservative.
        extra_bits = 4 * self.rank_width if extra_bits is None else extra_bits
        bits = self.materialized_bits + self.pivots * self.rank_width + extra_bits
        cols = self.materialized_columns + self.pivots + extra_columns
        if bits > self.budget.max_live_matrix_bits:
            raise ResourceLimit('live matrix-bit envelope exceeded')
        if cols > self.budget.max_live_columns:
            raise ResourceLimit('live matrix/pivot column limit exceeded')
        self.peak('peak_live_matrix_bit_upper_bound', bits)
        self.peak('peak_live_columns', cols)


def bounded_compositions(caps: tuple[int, ...], total: int,
                         suffix: tuple[int, ...] | None = None) -> Iterator[tuple[int, ...]]:
    """Enumerate 0 <= a_j <= caps[j], sum(a_j)=total, without product rescans.

    Iterative depth-first search avoids dependence on Python's recursion limit.
    Every visited prefix extends to an output: suffix capacities prune before
    descent.  Across all totals the output work is O(t prod_j(caps[j]+1)).
    The optional suffix vector is internal reuse; callers must supply its exact
    suffix sums.  ``caps`` and ``total`` are nonnegative integers.
    """
    t = len(caps)
    if suffix is None:
        values = [0] * (t + 1)
        for j in range(t - 1, -1, -1):
            values[j] = values[j + 1] + caps[j]
        suffix = tuple(values)
    if total < 0 or total > suffix[0]:
        return
    if not t:
        if total == 0:
            yield ()
        return
    state = [0] * t
    remaining = [0] * (t + 1)
    remaining[0] = total
    next_value = [0] * t
    high = [0] * t
    depth = 0
    next_value[0] = max(0, total - suffix[1])
    high[0] = min(caps[0], total)
    while depth >= 0:
        if next_value[depth] > high[depth]:
            depth -= 1
            continue
        value = next_value[depth]
        next_value[depth] += 1
        state[depth] = value
        rest = remaining[depth] - value
        if depth == t - 1:
            # The suffix bound at the last coordinate makes rest exactly zero.
            yield tuple(state)
            continue
        depth += 1
        remaining[depth] = rest
        next_value[depth] = max(0, rest - suffix[depth + 1])
        high[depth] = min(caps[depth], rest)


class _Cache:
    """Weighted LRU; no unbounded support or map-key history is retained."""

    def __init__(self, entries: int, slots: int, meter: _Meter, prefix: str,
                 slot_name: str):
        self.entries = entries
        self.capacity = slots
        self.meter = meter
        self.prefix = prefix
        self.slot_name = slot_name
        self.items: OrderedDict = OrderedDict()
        self.slots = 0

    def get(self, key):
        if key not in self.items:
            return None
        value, size = self.items.pop(key)
        self.items[key] = (value, size)
        self.meter.stats[self.prefix + '_cache_hits'] += 1
        return value

    def put(self, key, value, size: int):
        if not self.entries or size > self.capacity:
            return
        while self.items and (len(self.items) >= self.entries
                              or self.slots + size > self.capacity):
            _, (_, old_size) = self.items.popitem(last=False)
            self.slots -= old_size
        self.items[key] = (value, size)
        self.slots += size
        self.meter.peak(self.prefix + '_cache_entries_peak', len(self.items))
        self.meter.peak(self.prefix + '_cache_' + self.slot_name + '_peak', self.slots)


@dataclass(frozen=True)
class _Map:
    # kind: 0=zero, 1=dot, 2=merge, 3=split.  Store circle indexes rather than
    # exponentially sized relabel tables or one-hot integers in the cache.
    kind: int
    relabel: tuple[int, ...] = ()
    first: int = -1
    second: int = -1
    split: int = -1

    @property
    def slots(self) -> int:
        # Counts the four scalar fields and the relabel integer slots.
        return 4 + len(self.relabel)

    def images(self, label: int) -> tuple[int, ...]:
        if self.kind == 0:
            return ()
        if self.kind == 1:
            bits = tuple(1 << (circle - 1) for circle in (self.first, self.second)
                         if circle > 0)
            return tuple(label | bit for bit in bits if not label & bit)
        xmask = (label << 1) | 1
        y = 0
        rest = xmask
        while rest:
            low = rest & -rest
            circle = self.relabel[low.bit_length() - 1]
            bit = 0 if circle < 0 else 1 << circle
            if self.kind == 2 and y & bit:
                return ()
            y |= bit
            rest ^= low
        if self.kind == 2:
            return (y >> 1,)
        first, second = 1 << self.first, 1 << self.second
        if xmask & (1 << self.split):
            return ((y | first | second) >> 1,)
        return ((y | first) >> 1, (y | second) >> 1)


def _compile_saddle(source: Geometry, target: Geometry) -> _Map:
    relation = [{target.owner[v] for v in c} for c in source.circles]
    nc, nd = len(source.circles), len(target.circles)
    if nc == nd + 1:
        if any(len(targets) != 1 for targets in relation):
            raise ArithmeticError('invalid merge relation')
        return _Map(2, tuple(next(iter(x)) for x in relation))
    if nd == nc + 1:
        split = [j for j, targets in enumerate(relation) if len(targets) == 2]
        if len(split) != 1:
            raise ArithmeticError('invalid split relation')
        j = split[0]
        if any(len(targets) != 1 for k, targets in enumerate(relation) if k != j):
            raise ArithmeticError('invalid unaffected circle')
        a, b = sorted(relation[j])
        relabel = tuple(-1 if k == j else next(iter(targets))
                        for k, targets in enumerate(relation))
        return _Map(3, relabel, a, b, j)
    raise ArithmeticError('a classical saddle must merge or split one circle')


def _compile_dot(geometry: Geometry, a: int, b: int) -> _Map:
    ca, cb = geometry.owner[a], geometry.owner[b]
    if ca == cb:
        return _Map(0)
    return _Map(1, first=ca, second=cb)


@dataclass(frozen=True)
class _State:
    offset: int
    support: int
    dimension: int


@dataclass
class _Layer:
    degree: int
    states: dict[tuple[int, ...], _State]
    dimension: int


class _Engine:
    def __init__(self, strands: int, runs: tuple[Run, ...], meter: _Meter):
        self.strands = strands
        self.runs = runs
        self.meter = meter
        self.caps = tuple(abs(r.exponent) for r in runs)
        suffix = [0] * (len(runs) + 1)
        for j in range(len(runs) - 1, -1, -1):
            suffix[j] = suffix[j + 1] + self.caps[j]
        self.suffix = tuple(suffix)
        self.negative = sum(m for m, r in zip(self.caps, runs) if r.exponent < 0)
        cap = meter.budget
        count = 1
        if count > cap.max_states:
            raise ResourceLimit('macro state limit exceeded')
        for m in self.caps:
            meter.check()
            # Saturating comparison precedes multiplication or decimal output.
            if m + 1 > cap.max_states // count:
                raise ResourceLimit('macro state limit exceeded')
            count *= m + 1
        self.vertices = (len(runs) + 1) * strands
        if self.vertices > cap.max_grid_vertices:
            raise ResourceLimit('topology grid vertex limit exceeded')
        self.geometries = _Cache(cap.max_geometry_cache_entries,
                                 cap.max_geometry_cache_vertices, meter,
                                 'geometry', 'vertices')
        self.maps = _Cache(cap.max_map_cache_entries, cap.max_map_cache_slots,
                           meter, 'map', 'slots')
        meter.stats.update(crossings=self.suffix[0], runs=len(runs),
                           macro_states=count, topology_grid_vertices=self.vertices)

    def geometry(self, support: int) -> Geometry:
        geometry = self.geometries.get(support)
        if geometry is None:
            self.meter.check()
            geometry = _geometry(self.strands, self.runs, support)
            self.meter.stats['geometry_builds'] += 1
            self.geometries.put(support, geometry, self.vertices)
        return geometry

    def layer(self, total: int) -> _Layer:
        meter, cap = self.meter, self.meter.budget
        layer = _Layer(total - self.negative, {}, 0)
        meter.live_layers += 1
        meter.peak('peak_live_layers', meter.live_layers)
        for state in bounded_compositions(self.caps, total, self.suffix):
            meter.check()
            if meter.live_states >= cap.max_live_states:
                raise ResourceLimit('live state-index limit exceeded')
            support = sum(1 << j for j, (a, m, r) in enumerate(
                zip(state, self.caps, self.runs)) if (a if r.exponent > 0 else m - a))
            geometry = self.geometry(support)
            exponent = len(geometry.circles) - 1
            # Guard a potentially huge shift before constructing the dimension.
            if exponent >= min(cap.max_basis, cap.max_layer_basis).bit_length():
                raise ResourceLimit('single-state basis dimension exceeds budget')
            dimension = 1 << exponent
            if layer.dimension + dimension > cap.max_layer_basis:
                raise ResourceLimit('layer basis limit exceeded')
            if meter.stats['basis'] + dimension > cap.max_basis:
                raise ResourceLimit('total enumerated basis limit exceeded')
            layer.states[state] = _State(layer.dimension, support, dimension)
            layer.dimension += dimension
            meter.live_states += 1
            meter.stats['enumerated_macro_states'] += 1
            meter.stats['basis'] += dimension
            meter.peak('peak_live_states', meter.live_states)
        meter.peak('peak_chain_dimension', layer.dimension)
        return layer

    def release(self, layer: _Layer):
        self.meter.live_states -= len(layer.states)
        self.meter.live_layers -= 1
        # Clear eagerly: generator frames or local aliases cannot retain states.
        layer.states.clear()

    def edge_map(self, support: int, j: int, saddle: bool,
                 source: Geometry, target_support: int) -> _Map:
        key = (support, j, saddle)
        compiled = self.maps.get(key)
        if compiled is None:
            if saddle:
                compiled = _compile_saddle(source, self.geometry(target_support))
            else:
                i = self.runs[j].generator - 1
                compiled = _compile_dot(source, j * self.strands + i,
                                        (j + 1) * self.strands + i)
            self.meter.stats['map_compilations'] += 1
            self.maps.put(key, compiled, compiled.slots)
        return compiled

    def columns(self, source: _Layer, target: _Layer | None) -> Iterator[int]:
        meter = self.meter
        if target is None:
            for _ in range(source.dimension):
                meter.check()
                yield 0
            return
        for state, info in source.states.items():
            meter.check()
            geometry = self.geometry(info.support)
            edges: list[tuple[int, _Map]] = []
            active_slots = 0
            for j, (a, m, run) in enumerate(zip(state, self.caps, self.runs)):
                if a == m:
                    continue
                target_state = state[:j] + (a + 1,) + state[j + 1:]
                target_info = target.states[target_state]
                k = a if run.exponent > 0 else m - a
                kk = k + 1 if run.exponent > 0 else k - 1
                compiled = self.edge_map(info.support, j, not k or not kk,
                                         geometry, target_info.support)
                if compiled.kind == 0:
                    continue
                if active_slots + compiled.slots > meter.budget.max_active_map_slots:
                    raise ResourceLimit('active compact-map slot limit exceeded')
                active_slots += compiled.slots
                edges.append((target_info.offset, compiled))
            meter.peak('active_map_slots_peak', active_slots)
            meter.peak('active_edges_peak', len(edges))
            for label in range(info.dimension):
                meter.check()
                meter.algebra_check()
                column = 0
                for offset, compiled in edges:
                    for q in compiled.images(label):
                        column ^= 1 << (offset + q)
                        meter.stats['differential_entries'] += 1
                yield column


def _rank(columns: Iterable[int], rows: int, meter: _Meter) -> int:
    pivots: dict[int, int] = {}
    meter.rank_width = rows
    meter.algebra_check()
    for column in columns:
        meter.check()
        while column:
            p = column.bit_length() - 1
            if p >= rows:
                raise ArithmeticError('differential column exceeds its row dimension')
            if p not in pivots:
                meter.pivots += 1
                meter.algebra_check()
                pivots[p] = column
                meter.pivot_bits += column.bit_length()
                meter.peak('peak_pivot_count', meter.pivots)
                meter.peak('peak_pivot_bit_length_sum', meter.pivot_bits)
                break
            column ^= pivots[p]
            meter.xor()
    result = len(pivots)
    meter.pivots = 0
    meter.pivot_bits = 0
    meter.rank_width = 0
    return result


def _record(columns: Iterable[int], result: list[int], rows: int,
            meter: _Meter) -> Iterator[int]:
    for column in columns:
        meter.materialized_columns += 1
        meter.materialized_bits += rows
        meter.algebra_check()
        result.append(column)
        meter.peak('peak_materialized_matrix_columns', meter.materialized_columns)
        meter.peak('peak_materialized_matrix_bit_upper_bound', meter.materialized_bits)
        yield column


def _verify_pair(previous: list[int], current: list[int], middle_dimension: int,
                 target_dimension: int, meter: _Meter, degree: int):
    # Include traversal/low-bit arithmetic and output temporaries in addition
    # to retained matrices.  This intentionally overcounts aliasing integers.
    meter.algebra_check(extra_bits=4 * middle_dimension + 3 * target_dimension,
                        extra_columns=7)
    for original in previous:
        meter.check()
        column, image = original, 0
        while column:
            low = column & -column
            j = low.bit_length() - 1
            if j >= len(current):
                raise ArithmeticError('d-squared matrix shape mismatch')
            image ^= current[j]
            column ^= low
            meter.xor()
        if image:
            raise ArithmeticError(f'd^2 != 0 in degree {degree}')


def _compute(strands: int, runs: tuple[Run, ...], budget: StreamBudget,
             check_d2: bool, stop_after_rank: int | None) -> dict:
    started = monotonic()
    meter = _Meter(budget)
    meter.check()
    engine = _Engine(strands, runs, meter)
    maximum_total = engine.suffix[0]
    source = engine.layer(0)
    dimensions: dict[int, int] = {source.degree: source.dimension}
    ranks: dict[int, int] = {}
    homology_degrees: dict[int, int] = {}
    cumulative = 0
    previous_rank = 0
    previous_columns: list[int] | None = None
    previous_rows = 0
    complete = True
    checked_through: int | None = None
    finalized_through = source.degree - 1
    for total in range(maximum_total + 1):
        target = engine.layer(total + 1) if total < maximum_total else None
        rows = target.dimension if target is not None else 0
        if target is not None:
            dimensions[target.degree] = rows
        meter.stats['matrix_bit_upper_bound'] += source.dimension * rows
        meter.stats['rank_xor_bit_upper_bound'] += (
            source.dimension * rows * min(source.dimension, rows))
        columns = engine.columns(source, target)
        current_columns: list[int] | None = [] if check_d2 else None
        if current_columns is not None:
            columns = _record(columns, current_columns, rows, meter)
        rank = _rank(columns, rows, meter)
        ranks[source.degree] = rank
        if previous_columns is not None:
            _verify_pair(previous_columns, current_columns, source.dimension,
                         rows, meter, source.degree - 1)
            checked_through = source.degree - 1
            meter.materialized_bits -= len(previous_columns) * previous_rows
            meter.materialized_columns -= len(previous_columns)
            previous_columns.clear()
        beta = source.dimension - previous_rank - rank
        if beta < 0:
            raise ArithmeticError('negative homology dimension')
        if beta:
            homology_degrees[source.degree] = beta
        cumulative += beta
        finalized_through = source.degree
        previous_rank = rank
        previous_columns = current_columns
        previous_rows = rows
        engine.release(source)
        if stop_after_rank is not None and cumulative > stop_after_rank and target is not None:
            complete = False
            engine.release(target)
            break
        if target is not None:
            source = target
    meter.check()
    stats = dict(meter.stats)
    stats['elimination_and_check_xors'] = meter.xors
    stats['peak_state_tuple_slots'] = stats['peak_live_states'] * len(runs)
    # Cache geometries plus a source/target or a new construction in flight.
    stats['geometry_vertex_live_bound'] = (
        stats['geometry_cache_vertices_peak'] + 2 * engine.vertices)
    stats['compact_map_slot_live_bound'] = (
        stats['map_cache_slots_peak'] + stats['active_map_slots_peak']
        + 2 * (engine.vertices + 4))
    return {
        'reduced_rank': cumulative if complete else None,
        'reduced_rank_lower_bound': cumulative,
        'by_degree': homology_degrees,
        'chain_dimensions': dimensions,
        'boundary_ranks': ranks,
        'components': components(strands, runs),
        'homology_complete': complete,
        'finalized_through_degree': finalized_through,
        'stats': stats,
        'seconds': monotonic() - started,
        'd_squared_checked': bool(check_d2 and complete),
        'd_squared_checked_through_degree': checked_through,
    }


def homology(strands: int, runs: Iterable[Run], *, budget: StreamBudget | None = None,
             check_d2: bool = False) -> dict:
    """Compute every homological degree exactly, with bounded live storage."""
    runs = validate_runs(strands, runs)
    return _compute(strands, runs, budget or StreamBudget(), check_d2, None)


def recognize(strands: int, runs: Iterable[Run], *, budget: StreamBudget | None = None,
              check_d2: bool = False, early_exit: bool = True) -> dict:
    """One-component recognition; finalized homology >1 certifies KNOTTED.

    An early result has ``reduced_rank=None`` and reports a rigorous lower
    bound.  ``early_exit=False`` computes the same full homology as homology().
    """
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError('unknot recognition requires a one-component braid closure')
    try:
        result = _compute(strands, runs, budget or StreamBudget(), check_d2,
                          1 if early_exit else None)
    except (ResourceLimit, MemoryError) as exc:
        return {
            'status': 'UNKNOWN', 'method': 'twist-khovanov-F2-streaming',
            'reason': str(exc) or 'memory allocation failed',
            'unrestricted_quasipolynomial_guarantee': False,
        }
    return {
        'status': 'UNKNOT' if result['reduced_rank'] == 1 else 'KNOTTED',
        'method': 'twist-khovanov-F2-streaming', 'homology': result,
        'unrestricted_quasipolynomial_guarantee': False,
    }
