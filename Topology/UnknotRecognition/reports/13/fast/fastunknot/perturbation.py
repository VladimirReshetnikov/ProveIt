"""Exact minimal models via a finite homological perturbation series.

Research backend, not the default scanner.  First contract the constant-term
differential over F2, then lift it through the positive-degree ideal of the
matching category.  At a boundary of w endpoints that ideal has power w+1 zero.
Optional certificates verify all deformation-retraction identities exactly.

Maps store one dict per source object: target -> bit-packed cobordism.  Objects
and coefficients use the same Planar instance as a FastScan snapshot.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from time import monotonic

from .geometry import ScanLimit
from .ordering import best_scan_order, validate_order
from .scan_fast import CAP, FastScan


@dataclass(frozen=True)
class Space:
    matching: tuple[int, ...]
    degree: tuple[int, ...]

    def __len__(self):
        return len(self.matching)


@dataclass
class Map:
    source: Space
    target: Space
    rows: list[dict[int, int]]

    def __bool__(self):
        return any(self.rows)


def zero(source, target):
    return Map(source, target, [{} for _ in source.matching])


def identity(space):
    return Map(space, space, [{i: 1} for i in range(len(space))])


def add(first, second):
    if first.source != second.source or first.target != second.target:
        raise ValueError("incompatible map addition")
    result = [row.copy() for row in first.rows]
    for row, other in zip(result, second.rows):
        for target, value in other.items():
            value ^= row.get(target, 0)
            if value:
                row[target] = value
            else:
                row.pop(target, None)
    return Map(first.source, first.target, result)


class Arithmetic:
    def __init__(self, algebra, deadline=None):
        self.algebra, self.deadline = algebra, deadline
        self.products = self.scalar_products = self.map_products = 0
        self.cache = {}

    def check(self):
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted in perturbation reduction")

    def compose(self, first, second):
        """Return second after first, including all exact F2 cancellations."""
        if first.target != second.source:
            raise ValueError("incompatible map composition")
        self.map_products += 1
        result = zero(first.source, second.target)
        source, middle, target = (first.source.matching,
                                  first.target.matching, second.target.matching)
        for a, row in enumerate(first.rows):
            if not a & 127:
                self.check()
            accum = result.rows[a]
            for b, f in row.items():
                for c, g in second.rows[b].items():
                    if f == 1 and source[a] == middle[b]:
                        value = g
                        self.scalar_products += 1
                    elif g == 1 and middle[b] == target[c]:
                        value = f
                        self.scalar_products += 1
                    else:
                        self.products += 1
                        key = (source[a], middle[b], target[c], f, g)
                        value = self.cache.get(key)
                        if value is None:
                            value = self.cache[key] = self.algebra.compose(*key)
                    if value:
                        value ^= accum.get(c, 0)
                        if value:
                            accum[c] = value
                        else:
                            accum.pop(c, None)
        return result


def snapshot(scan):
    live = [i for i, ma in enumerate(scan.mid) if ma is not None]
    index = {old: new for new, old in enumerate(live)}
    space = Space(tuple(scan.mid[i] for i in live),
                  tuple(scan.deg[i] for i in live))
    differential = Map(space, space, [
        {index[j]: f for j, f in scan.out[i].items()} for i in live])
    return space, differential


def _bits(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def _independent_add(pivots, vector):
    while vector:
        top = vector.bit_length() - 1
        if top not in pivots:
            pivots[top] = vector
            return True
        vector ^= pivots[top]
    return False


def _column_data(columns):
    """Independent original columns, their indices, and a kernel basis."""
    pivots, images, sources, kernel = {}, [], [], []
    for j, column in enumerate(columns):
        value, relation = column, 1 << j
        while value:
            top = value.bit_length() - 1
            if top not in pivots:
                pivots[top] = (value, relation)
                images.append(column)
                sources.append(j)
                break
            old, combination = pivots[top]
            value ^= old
            relation ^= combination
        else:
            kernel.append(relation)
    return images, sources, kernel


def _coordinate_solver(basis, dimension):
    pivots = {}
    for j, vector in enumerate(basis):
        coordinates = 1 << j
        while vector:
            top = vector.bit_length() - 1
            if top not in pivots:
                pivots[top] = (vector, coordinates)
                break
            old, combination = pivots[top]
            vector ^= old
            coordinates ^= combination
        else:
            raise ArithmeticError("dependent contraction basis")
    if len(pivots) != dimension:
        raise ArithmeticError("incomplete contraction basis")

    def solve(vector):
        coordinates = 0
        while vector:
            top = vector.bit_length() - 1
            old, combination = pivots[top]
            vector ^= old
            coordinates ^= combination
        return coordinates

    return solve


def scalar_contraction(space, differential, check=lambda: None):
    """Construct d0,i,p,h with d0*h+h*d0=1+i*p and side conditions.

    Each (matching, homological degree) block is split as boundaries, homology,
    and a complement to cycles.  All map entries are scalar identities.
    """
    groups = defaultdict(list)
    for i, key in enumerate(zip(space.matching, space.degree)):
        groups[key].append(i)
    d0 = zero(space, space)
    for a, row in enumerate(differential.rows):
        for b, value in row.items():
            if space.matching[a] == space.matching[b] and value & 1:
                d0.rows[a][b] = 1
    data = {}
    for (matching, degree), objects in groups.items():
        check()
        targets = groups.get((matching, degree + 1), [])
        positions = {obj: j for j, obj in enumerate(targets)}
        columns = [sum(1 << positions[b] for b in d0.rows[a]) for a in objects]
        data[matching, degree] = _column_data(columns)
    hm, hd, inclusion_rows = [], [], []
    projection_rows, homotopy_rows = ([{} for _ in space.matching],
                                      [{} for _ in space.matching])
    profile = []
    for matching, degree in sorted(groups, key=lambda key: (key[1], key[0])):
        check()
        objects = groups[matching, degree]
        boundaries, incoming_sources, _ = data.get((matching, degree - 1), ([], [], []))
        _, outgoing_sources, kernel = data[matching, degree]
        basis = list(boundaries)
        independent = {}
        for vector in boundaries:
            if not _independent_add(independent, vector):
                raise ArithmeticError("dependent boundary basis")
        homology_vectors = []
        for vector in kernel:
            if _independent_add(independent, vector):
                basis.append(vector)
                homology_vectors.append(vector)
        base = len(hm)
        for vector in homology_vectors:
            hm.append(matching)
            hd.append(degree)
            inclusion_rows.append({objects[j]: 1 for j in _bits(vector)})
        basis.extend(1 << j for j in outgoing_sources)
        solve = _coordinate_solver(basis, len(objects))
        previous = groups.get((matching, degree - 1), [])
        nb, nh = len(boundaries), len(homology_vectors)
        for local, obj in enumerate(objects):
            coefficients = solve(1 << local)
            projection_rows[obj] = {
                base + j: 1 for j in range(nh) if coefficients & (1 << (nb + j))}
            homotopy_rows[obj] = {
                previous[incoming_sources[j]]: 1
                for j in range(nb) if coefficients & (1 << j)}
        profile.append({"matching_id": matching, "degree": degree,
                        "input_objects": len(objects), "incoming_rank": nb,
                        "outgoing_rank": len(outgoing_sources), "minimal_objects": nh})
    reduced = Space(tuple(hm), tuple(hd))
    inclusion = Map(reduced, space, inclusion_rows)
    projection = Map(space, reduced, projection_rows)
    homotopy = Map(space, space, homotopy_rows)
    return d0, inclusion, projection, homotopy, profile


def _assert_zero(value, description):
    if value:
        raise ArithmeticError(description)


def verify_contraction(differential, minimal, inclusion, projection, homotopy, arithmetic):
    """All identities checked over the actual cobordism algebra, no rank oracle."""
    compose = arithmetic.compose
    _assert_zero(compose(differential, differential), "input differential does not square to zero")
    _assert_zero(compose(minimal, minimal), "minimal differential does not square to zero")
    _assert_zero(add(compose(inclusion, differential), compose(minimal, inclusion)),
                 "inclusion is not a chain map")
    _assert_zero(add(compose(differential, projection), compose(projection, minimal)),
                 "projection is not a chain map")
    _assert_zero(add(compose(inclusion, projection), identity(minimal.source)),
                 "projection-inclusion is not identity")
    _assert_zero(add(add(compose(homotopy, differential), compose(differential, homotopy)),
                     add(identity(differential.source), compose(projection, inclusion))),
                 "deformation-retraction identity failed")
    _assert_zero(compose(inclusion, homotopy), "homotopy-inclusion is nonzero")
    _assert_zero(compose(homotopy, projection), "projection-homotopy is nonzero")
    _assert_zero(compose(homotopy, homotopy), "homotopy does not square to zero")
    return True


def minimal_model(scan, *, certificate=False):
    """Return a minimal complex and, optionally, its checked contraction maps."""
    space, differential = snapshot(scan)
    arithmetic = Arithmetic(scan.algebra, scan.deadline)
    d0, i0, p0, h0, profile = scalar_contraction(space, differential, arithmetic.check)
    delta = add(differential, d0)
    width = len(scan.points)
    compose = arithmetic.compose
    inclusion, term, depth = i0, i0, 0
    for power in range(1, width + 1):
        term = compose(compose(term, delta), h0)
        if not term:
            break
        inclusion = add(inclusion, term)
        depth = power
    if certificate:
        _assert_zero(compose(compose(term, delta), h0), "radical nilpotence bound failed")
    minimal = compose(compose(inclusion, delta), p0)
    for a, row in enumerate(minimal.rows):
        for b, value in row.items():
            if minimal.source.matching[a] == minimal.source.matching[b] and value & 1:
                raise ArithmeticError("lifted model still has a scalar unit")
    result = {"space": minimal.source, "differential": minimal, "profile": profile,
              "stats": {"input_objects": len(space), "minimal_objects": len(minimal.source),
                        "boundary": width, "perturbation_depth": depth,
                        "algebra_products": arithmetic.products,
                        "scalar_products": arithmetic.scalar_products,
                        "map_products": arithmetic.map_products}, "certified": False}
    if certificate:
        right = compose(h0, delta)
        projection, pterm = p0, p0
        homotopy, hterm = h0, h0
        for _ in range(width):
            pterm = compose(right, pterm)
            hterm = compose(right, hterm)
            projection = add(projection, pterm)
            homotopy = add(homotopy, hterm)
            if not pterm and not hterm:
                break
        _assert_zero(compose(right, pterm), "projection series failed nilpotence")
        _assert_zero(compose(right, hterm), "homotopy series failed nilpotence")
        verify_contraction(differential, minimal, inclusion, projection, homotopy, arithmetic)
        result.update(inclusion=inclusion, projection=projection, homotopy=homotopy, certified=True)
    return result


def install(scan, model):
    """Continue the scan from the exact minimal model, retaining its Planar cache."""
    space, differential = model["space"], model["differential"]
    scan.mid, scan.deg = list(space.matching), list(space.degree)
    scan.out = [row.copy() for row in differential.rows]
    scan.inc = [set() for _ in scan.mid]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    removed = scan.live - len(space)
    if removed < 0 or removed % 2:
        raise ArithmeticError("invalid minimal-model dimension")
    scan.stats["eliminations"] += removed // 2
    scan.live = len(space)
    scan.stats["max_objects_after_elimination"] = max(
        scan.stats["max_objects_after_elimination"], scan.live)
    scan.composed = {}
    scan.small = [[] for _ in range(CAP)]


def khovanov_perturbation(pd, *, order=None, max_objects=None, seconds=None, certificate=False):
    """Full F2 rank through the research backend; not a speed recommendation."""
    pd = [tuple(row) for row in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return {"rank": 2, "reduced_rank": 1, "by_degree": {0: 2}, "stats": {}, "order": []}
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12))
    scan = FastScan(max_objects=max_objects, deadline=deadline, shape_cache=False)
    totals = {"algebra_products": 0, "scalar_products": 0, "map_products": 0,
              "max_perturbation_depth": 0}
    for crossing in order:
        scan.add_crossing(pd[crossing], reduce_now=False)
        model = minimal_model(scan, certificate=certificate)
        for key in ("algebra_products", "scalar_products", "map_products"):
            totals[key] += model["stats"][key]
        totals["max_perturbation_depth"] = max(totals["max_perturbation_depth"],
                                              model["stats"]["perturbation_depth"])
        install(scan, model)
    rank = scan.total_rank()
    if rank % 2:
        raise ArithmeticError("odd unreduced rank for a knot")
    return {"rank": rank, "reduced_rank": rank // 2, "by_degree": scan.ranks_by_degree(),
            "stats": dict(scan.stats, **totals), "order": order, "certified": certificate}
