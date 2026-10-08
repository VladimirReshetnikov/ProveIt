"""Finite radical-first reduction of delooped F2 cobordism complexes.

No knot verdict is produced here. The caller supplies a valid chain complex in
one fixed-frontier category with the Planar coefficient convention. All work is
exact. The returned object is committed by the adapter only after success.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from typing import Callable
from disk_frontier import verify_common_order


def bits(value: int):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def xor_at(row: dict[int, int], key: int, value: int):
    if not value:
        return
    value ^= row.get(key, 0)
    if value:
        row[key] = value
    else:
        row.pop(key, None)


class BinaryBasis:
    """Column echelon basis, retaining coordinates in the supplied generators."""
    def __init__(self):
        self.pivots: dict[int, tuple[int, int]] = {}

    def reduce(self, value: int, coordinates: int = 0) -> tuple[int, int]:
        while value:
            top = value.bit_length() - 1
            pivot = self.pivots.get(top)
            if pivot is None:
                break
            value ^= pivot[0]
            coordinates ^= pivot[1]
        return value, coordinates

    def add(self, value: int, coordinates: int = 0) -> tuple[bool, int, int]:
        value, coordinates = self.reduce(value, coordinates)
        if not value:
            return False, value, coordinates
        self.pivots[value.bit_length() - 1] = (value, coordinates)
        return True, value, coordinates

    def solve(self, value: int) -> int:
        residual, coordinates = self.reduce(value)
        if residual:
            raise ArithmeticError("incomplete binary basis")
        return coordinates


def apply_binary(columns: list[int], vector: int) -> int:
    value = 0
    for j in bits(vector):
        value ^= columns[j]
    return value


@dataclass
class Complex:
    mid: list[int]
    deg: list[int]
    out: list[dict[int, int]]

    @property
    def n(self) -> int:
        return len(self.mid)

    def validate(self):
        if len(self.deg) != self.n or len(self.out) != self.n:
            raise ValueError("inconsistent object arrays")
        if any(type(m) is not int or m < 0 for m in self.mid) or any(type(h) is not int for h in self.deg):
            raise ValueError("matching IDs and homological degrees must be integers")
        for j, row in enumerate(self.out):
            for k, f in row.items():
                if not 0 <= k < self.n or self.deg[k] != self.deg[j] + 1:
                    raise ValueError("invalid differential target or homological degree")
                if type(f) is not int or f <= 0:
                    raise ValueError("differentials must contain positive packed coefficients")


def snapshot(scan) -> Complex:
    live = [j for j, m in enumerate(scan.mid) if m is not None]
    index = {j: k for k, j in enumerate(live)}
    return Complex([scan.mid[j] for j in live], [scan.deg[j] for j in live],
                   [{index[k]: f for k, f in scan.out[j].items()} for j in live])


def scalar_part(c: Complex) -> list[int]:
    """Bit zero is a scalar ONLY when source and target matchings are equal."""
    return [sum(1 << k for k, f in row.items() if c.mid[j] == c.mid[k] and f & 1)
            for j, row in enumerate(c.out)]


def binary_profile(c: Complex, poll: Callable[[], None] = lambda: None):
    """Exact minimal multiplicity profile without constructing any cobordism."""
    c.validate()
    d0 = scalar_part(c)
    ranks = defaultdict(int)
    groups = defaultdict(list)
    for j in range(c.n):
        groups[c.mid[j], c.deg[j]].append(j)
    for key, group in groups.items():
        basis = BinaryBasis()
        for j in group:
            poll()
            if apply_binary(d0, d0[j]):
                raise ArithmeticError("the scalar quotient does not square to zero")
            basis.add(d0[j])
        ranks[key] = len(basis.pivots)
    result = {}
    for (m, degree), group in groups.items():
        value = len(group) - ranks[m, degree] - ranks[m, degree - 1]
        if value < 0:
            raise ArithmeticError("negative scalar homology dimension")
        if value:
            result[m, degree] = value
    return result


@dataclass
class Contraction:
    d0: list[int]
    i: list[int]        # columns: residual -> original
    p: list[int]        # columns: original -> residual
    h: list[int]        # columns: original -> original, degree -1
    mid: list[int]
    deg: list[int]

    @property
    def r(self):
        return len(self.i)

    def verify(self):
        n = len(self.d0)
        if len(self.h)!=n or len(self.p)!=n or len(self.mid)!=self.r or len(self.deg)!=self.r:
            raise ArithmeticError("binary contraction dimensions disagree")
        for vectors,bound in ((self.d0,n),(self.h,n),(self.i,n),(self.p,self.r)):
            if any(type(v) is not int or v<0 or v.bit_length()>bound for v in vectors):
                raise ArithmeticError("binary contraction has an invalid vector")
        for j in range(n):
            if apply_binary(self.d0, self.d0[j]):
                raise ArithmeticError("d0 squared")
            if (apply_binary(self.d0, self.h[j]) ^ apply_binary(self.h, self.d0[j])
                    ^ apply_binary(self.i, self.p[j])) != 1 << j:
                raise ArithmeticError("scalar contraction identity")
            if apply_binary(self.h, self.h[j]) or apply_binary(self.p, self.h[j]):
                raise ArithmeticError("scalar contraction side condition")
            if apply_binary(self.p, self.d0[j]):
                raise ArithmeticError("p d0")
        for j, v in enumerate(self.i):
            if apply_binary(self.p, v) != 1 << j:
                raise ArithmeticError("p i")
            if apply_binary(self.d0, v) or apply_binary(self.h, v):
                raise ArithmeticError("inclusion side condition")


def contract_scalar(c: Complex, poll: Callable[[], None] = lambda: None,
                    verify: bool = False) -> Contraction:
    c.validate()
    n = c.n
    d0 = scalar_part(c)
    groups = defaultdict(list)
    for j in range(n):
        groups[c.mid[j], c.deg[j]].append(j)
    boundaries = defaultdict(list)  # key -> (boundary, chosen preimage)
    kernels = {}
    lifts = {}
    for key in sorted(groups):
        basis = BinaryBasis()
        kernel, lift_list = [], []
        for j in groups[key]:
            poll()
            if apply_binary(d0, d0[j]):
                raise ArithmeticError("d0 squared is nonzero")
            independent, v, w = basis.add(d0[j], 1 << j)
            if independent:
                boundaries[key[0], key[1] + 1].append((v, w))
                lift_list.append(w)
            else:
                kernel.append(w)
        kernels[key], lifts[key] = kernel, lift_list
    i, p, h, mid, deg = [], [0] * n, [0] * n, [], []
    for key in sorted(groups):
        poll()
        b_data = boundaries[key]
        b_vectors = [v for v, _ in b_data]
        span = BinaryBasis()
        for v in b_vectors:
            if not span.add(v)[0]:
                raise ArithmeticError("dependent boundary basis")
        homology = []
        for v in kernels[key]:
            if span.add(v)[0]:
                homology.append(v)
        offset = len(i)
        i.extend(homology)
        mid.extend([key[0]] * len(homology))
        deg.extend([key[1]] * len(homology))
        complete = b_vectors + homology + lifts[key]
        if len(complete) != len(groups[key]):
            raise ArithmeticError("binary splitting dimension mismatch")
        basis = BinaryBasis()
        for k, v in enumerate(complete):
            if not basis.add(v, 1 << k)[0]:
                raise ArithmeticError("binary splitting is singular")
        nb = len(b_vectors)
        nh = len(homology)
        for j in groups[key]:
            poll()
            coordinates = basis.solve(1 << j)
            for k in bits(coordinates & ((1 << nb) - 1)):
                h[j] ^= b_data[k][1]
            p[j] = ((coordinates >> nb) & ((1 << nh) - 1)) << offset
    result = Contraction(d0, i, p, h, mid, deg)
    if verify:
        result.verify()
    return result


@dataclass
class Reduction:
    complex: Complex
    contraction: Contraction
    stats: dict
    inclusion: list[dict[int, int]] | None = None
    projection: list[dict[int, int]] | None = None
    homotopy: list[dict[int, int]] | None = None


def reduce_complex(c: Complex, algebra, *, contraction: Contraction | None = None,
                   compose=None, poll: Callable[[], None] = lambda: None,
                   certificate: bool = False, cache_limit: int = 4096, cyclic_order=None) -> Reduction:
    """Compute D = p delta sum (h delta)^k i using a finite radical series.

    The nilpotence bound is derived from the common frontier, not a heuristic
    iteration cutoff. Unexpected nontermination raises rather than truncates.
    """
    if type(cache_limit) is not int or cache_limit < 0:
        raise ValueError("cache_limit must be a nonnegative integer")
    c.validate()
    sc = contraction if contraction is not None else contract_scalar(c, poll)
    if any(m >= len(algebra.pairs) for m in c.mid):
        raise ValueError("unknown matching ID")
    frontier_sizes = {len(algebra.pairs[m]) for m in c.mid}
    if len(frontier_sizes) > 1:
        raise ValueError("objects have different frontier sizes")
    b = next(iter(frontier_sizes), 0)
    frontiers = {frozenset(x for pair in algebra.pairs[m] for x in pair) for m in c.mid}
    if len(frontiers) > 1:
        raise ValueError("objects do not share a frontier")
    frontier = next(iter(frontiers), frozenset())
    # A common cyclic order is a checked precondition, NEVER inferred merely
    # from the number of endpoints. Natural label order is only a candidate.
    cyclic_order = tuple(sorted(frontier)) if cyclic_order is None else tuple(cyclic_order)
    verify_common_order([algebra.pairs[m] for m in c.mid], cyclic_order)
    delta = []
    for j, row in enumerate(c.out):
        new = {}
        for k, f in row.items():
            if c.mid[j] == c.mid[k]:
                f &= ~1
            if f:
                limit = 1 << algebra.basis(c.mid[j], c.mid[k])[1]
                if f.bit_length() > limit:
                    raise ValueError("coefficient outside its Hom basis")
                new[k] = f
        delta.append(new)
    all_diagonal = all(c.mid[j] == c.mid[k] for j, row in enumerate(delta) for k in row)
    # Same-matching positive terms have degree >=2; otherwise use degree >=1.
    max_factors = b if all_diagonal else max(0, 2 * b - 1)
    stats = dict(objects=c.n, residual=sc.r, half_boundary=b,
                 radical_entries=sum(map(len, delta)), compositions=0, cache_hits=0,
                 scalar_xors=0, max_delta_factors=0, finite_bound=max_factors, cache_peak=0, cyclic_order=cyclic_order)
    cache = {}
    raw_compose = algebra.compose if compose is None else compose

    def product(a, middle, target, f, g):
        if f == 1 and a == middle:
            return g
        if g == 1 and middle == target:
            return f
        stats["compositions"] += 1
        key = (a, middle, target, f, g)
        if key in cache:
            stats["cache_hits"] += 1
            return cache[key]
        value = raw_compose(*key)
        if cache_limit:
            if len(cache) >= cache_limit:
                cache.clear()
            cache[key] = value
            stats["cache_peak"] = max(stats["cache_peak"], len(cache))
        return value

    def apply_delta(source_mid, vector):
        result = {}
        for j, f in vector.items():
            poll()
            for k, g in delta[j].items():
                xor_at(result, k, product(source_mid, c.mid[j], c.mid[k], f, g))
        return result

    def apply_scalar(columns, vector):
        result = {}
        for j, f in vector.items():
            for k in bits(columns[j]):
                stats["scalar_xors"] += 1
                xor_at(result, k, f)
        return result

    def series(source_mid, initial, need_d=False, keep_total=True):
        term = dict(initial)
        total, differential = {}, {}
        for depth in range(max_factors + 1):
            poll()
            if keep_total:
                for j, f in term.items():
                    xor_at(total, j, f)
            y = apply_delta(source_mid, term)
            if y:
                stats["max_delta_factors"] = max(stats["max_delta_factors"], depth + 1)
            if depth == max_factors and y:
                raise ArithmeticError("radical nilpotence bound violated")
            if need_d:
                for j, f in apply_scalar(sc.p, y).items():
                    xor_at(differential, j, f)
            term = apply_scalar(sc.h, y)
            if not term:
                return total, differential
        raise ArithmeticError("finite perturbation did not terminate")

    inclusion, out = [], []
    for j, v in enumerate(sc.i):
        lifted, differential = series(sc.mid[j], {k: 1 for k in bits(v)}, need_d=True,
                                      keep_total=certificate)
        if certificate:
            inclusion.append(lifted)
        out.append(differential)
    result_complex = Complex(list(sc.mid), list(sc.deg), out)
    result_complex.validate()
    for j, row in enumerate(out):
        if any(result_complex.mid[j] == result_complex.mid[k] and f & 1 for k, f in row.items()):
            raise ArithmeticError("transferred differential is not radical")
    result = Reduction(result_complex, sc, stats, inclusion if certificate else None)
    if certificate:
        homotopy, projection = [], []
        for j, v in enumerate(sc.h):
            lifted, _ = series(c.mid[j], {k: 1 for k in bits(v)})
            homotopy.append(lifted)
            pcol = {k: 1 for k in bits(sc.p[j])}
            for k, f in apply_scalar(sc.p, apply_delta(c.mid[j], lifted)).items():
                xor_at(pcol, k, f)
            projection.append(pcol)
        result.projection, result.homotopy = projection, homotopy
    return result


def compose_maps(left, middle, right, f, g, algebra):
    """Independent full sparse matrix multiplication g o f for verification."""
    result = []
    for j, row in enumerate(f):
        acc = {}
        for k, v in row.items():
            for z, w in g[k].items():
                xor_at(acc, z, algebra.compose(left[j], middle[k], right[z], v, w))
        result.append(acc)
    return result


def add_maps(*maps):
    if not maps:
        return []
    result = [dict() for _ in maps[0]]
    for mapping in maps:
        if len(mapping) != len(result):
            raise ValueError("map dimensions differ")
        for dest, row in zip(result, mapping):
            for k, f in row.items():
                xor_at(dest, k, f)
    return result


def verify_reduction(c: Complex, red: Reduction, algebra):
    """Check all strong deformation-retract identities, not just homology ranks."""
    small = red.complex
    I, P, H = red.inclusion, red.projection, red.homotopy
    if I is None or P is None or H is None:
        raise ValueError("full certificate was not requested")
    c.validate(); small.validate()
    verify_common_order([algebra.pairs[m] for m in c.mid + small.mid],
                        red.stats.get("cyclic_order", tuple(sorted(
                            {x for m in c.mid for pair in algebra.pairs[m] for x in pair}))))
    def typed(source, target, mapping, shift):
        if len(mapping) != source.n:
            raise ArithmeticError("certificate map has wrong source dimension")
        for j, row in enumerate(mapping):
            for k, f in row.items():
                if type(k) is not int or not 0 <= k < target.n:
                    raise ArithmeticError("certificate target is out of range")
                if target.deg[k] != source.deg[j] + shift:
                    raise ArithmeticError("certificate map has wrong homological degree")
                if type(f) is not int or f <= 0:
                    raise ArithmeticError("certificate coefficient is not canonical")
                limit = 1 << algebra.basis(source.mid[j], target.mid[k])[1]
                if f.bit_length() > limit:
                    raise ArithmeticError("certificate coefficient exceeds its Hom basis")
    typed(c,c,c.out,1);typed(small,small,small.out,1)
    typed(small,c,I,0);typed(c,small,P,0);typed(c,c,H,-1)
    C, R, d, D = c.mid, small.mid, c.out, small.out
    def mul(a, b, z, f, g):
        return compose_maps(a, b, z, f, g, algebra)
    def zero(mapping):
        return not any(mapping)
    idc = [{j: 1} for j in range(c.n)]
    idr = [{j: 1} for j in range(small.n)]
    checks = {
        "d2": zero(mul(C, C, C, d, d)),
        "D2": zero(mul(R, R, R, D, D)),
        "dI=ID": mul(R, C, C, I, d) == mul(R, R, C, D, I),
        "Pd=DP": mul(C, C, R, d, P) == mul(C, R, R, P, D),
        "PI=1": mul(R, C, R, I, P) == idr,
        "dH+Hd=1+IP": add_maps(mul(C, C, C, H, d), mul(C, C, C, d, H))
                          == add_maps(idc, mul(C, R, C, P, I)),
        "HI=0": zero(mul(R, C, C, I, H)),
        "PH=0": zero(mul(C, C, R, H, P)),
        "H2=0": zero(mul(C, C, C, H, H)),
    }
    failed = [key for key, value in checks.items() if not value]
    if failed:
        raise ArithmeticError("invalid reduction certificate: " + ", ".join(failed))
    return checks
