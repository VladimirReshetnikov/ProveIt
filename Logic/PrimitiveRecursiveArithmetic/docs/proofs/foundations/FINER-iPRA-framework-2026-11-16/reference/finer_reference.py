"""Exact reference algorithms for FINER-iPRA.

FINER = Finite-Interaction Normal form with Explicit Residuals.

This module is deliberately small and uses only the Python standard library.
It is a semantic reference implementation, not an iPRA proof checker and not a
replacement for the object-language Lean derivations described in the report.
All algorithms are finite and exact; rational arithmetic uses Fraction.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Hashable, Iterable, Mapping, Sequence, TypeVar

T = TypeVar("T", bound=Hashable)


def mixed_radix_encode(digits: Sequence[int], radices: Sequence[int]) -> int:
    """Encode digits in little-endian mixed radix.

    Preconditions: len(digits) == len(radices), each radix >= 1, and
    0 <= digit < radix. The empty vector encodes as 0.
    """
    if len(digits) != len(radices):
        raise ValueError("digits/radices length mismatch")
    code = 0
    place = 1
    for digit, radix in zip(digits, radices):
        if radix < 1:
            raise ValueError("radix must be positive")
        if not 0 <= digit < radix:
            raise ValueError("digit out of range")
        code += digit * place
        place *= radix
    return code


def mixed_radix_decode(code: int, radices: Sequence[int]) -> list[int]:
    """Decode the canonical digit vector for the given mixed radices."""
    if code < 0:
        raise ValueError("code must be nonnegative")
    digits: list[int] = []
    remaining = code
    for radix in radices:
        if radix < 1:
            raise ValueError("radix must be positive")
        digits.append(remaining % radix)
        remaining //= radix
    if remaining:
        raise ValueError("code exceeds mixed-radix range")
    return digits


def certificate_space_size(radices: Sequence[int]) -> int:
    size = 1
    for radix in radices:
        if radix < 1:
            raise ValueError("radix must be positive")
        size *= radix
    return size


@dataclass(frozen=True)
class SearchResult:
    bound: int
    code: int
    found: bool
    checked: int


def least_accepted(bound: int, checker: Callable[[int], bool]) -> SearchResult:
    """Return the least accepted code below bound, or bound on failure."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for code in range(bound):
        if checker(code):
            return SearchResult(bound=bound, code=code, found=True, checked=code + 1)
    return SearchResult(bound=bound, code=bound, found=False, checked=bound)


def verify_search_result(result: SearchResult, checker: Callable[[int], bool]) -> bool:
    if result.bound < 0 or result.code < 0:
        return False
    if result.found:
        return (
            result.code < result.bound
            and checker(result.code)
            and all(not checker(i) for i in range(result.code))
            and result.checked == result.code + 1
        )
    return (
        result.code == result.bound
        and all(not checker(i) for i in range(result.bound))
        and result.checked == result.bound
    )


Vector = tuple[int, ...]


@dataclass(frozen=True)
class DemandClosure:
    capacities: Vector
    trace: tuple[Vector, ...]
    closure: Vector
    stabilized_at: int


def _validate_vector(x: Sequence[int], capacities: Sequence[int]) -> Vector:
    if len(x) != len(capacities):
        raise ValueError("vector dimension mismatch")
    result = tuple(int(v) for v in x)
    for v, cap in zip(result, capacities):
        if cap < 0:
            raise ValueError("capacity must be nonnegative")
        if not 0 <= v <= cap:
            raise ValueError("coordinate outside finite box")
    return result


def monotone_demand_closure(
    capacities: Sequence[int],
    transformer: Callable[[Vector], Sequence[int]],
) -> DemandClosure:
    """Compute x_{t+1} = x_t join F(x_t) on a finite product of chains.

    The function does not attempt to decide monotonicity.  The returned trace
    is a certificate that can be checked independently.  If transformer is
    monotone, the theorem in the report proves that stabilization occurs by
    sum(capacities) strict increases and that the result is the least
    prefixed point.
    """
    caps = tuple(int(c) for c in capacities)
    if any(c < 0 for c in caps):
        raise ValueError("capacity must be nonnegative")
    x: Vector = tuple(0 for _ in caps)
    trace: list[Vector] = [x]
    max_steps = sum(caps) + 1
    for step in range(max_steps + 1):
        fx = _validate_vector(transformer(x), caps)
        nxt = tuple(max(a, b) for a, b in zip(x, fx))
        trace.append(nxt)
        if nxt == x:
            return DemandClosure(caps, tuple(trace), x, step)
        x = nxt
    raise RuntimeError("no stabilization within finite-box theorem bound")


def verify_demand_closure(
    cert: DemandClosure,
    transformer: Callable[[Vector], Sequence[int]],
) -> bool:
    caps = cert.capacities
    if not cert.trace or cert.trace[0] != tuple(0 for _ in caps):
        return False
    if cert.trace[-1] != cert.closure:
        return False
    for current, nxt in zip(cert.trace, cert.trace[1:]):
        try:
            fx = _validate_vector(transformer(current), caps)
        except ValueError:
            return False
        expected = tuple(max(a, b) for a, b in zip(current, fx))
        if nxt != expected:
            return False
    try:
        fcl = _validate_vector(transformer(cert.closure), caps)
    except ValueError:
        return False
    if any(f > c for f, c in zip(fcl, cert.closure)):
        return False
    strict_steps = sum(a != b for a, b in zip(cert.trace, cert.trace[1:]))
    if strict_steps > sum(caps):
        return False
    return cert.stabilized_at <= sum(caps)


def is_prefixed(x: Vector, transformer: Callable[[Vector], Sequence[int]]) -> bool:
    fx = tuple(transformer(x))
    return len(fx) == len(x) and all(a <= b for a, b in zip(fx, x))


def all_box_vectors(capacities: Sequence[int]) -> Iterable[Vector]:
    return product(*(range(c + 1) for c in capacities))


def verify_least_prefixed(
    closure: Vector,
    capacities: Sequence[int],
    transformer: Callable[[Vector], Sequence[int]],
) -> bool:
    if not is_prefixed(closure, transformer):
        return False
    for candidate in all_box_vectors(capacities):
        if is_prefixed(candidate, transformer):
            if any(c > y for c, y in zip(closure, candidate)):
                return False
    return True


@dataclass(frozen=True)
class ViabilityCertificate:
    layers: tuple[tuple[T, ...], ...]
    viable: tuple[frozenset[T], ...]
    path: tuple[T, ...] | None


def backward_viability(
    layers: Sequence[Sequence[T]],
    edge: Callable[[int, T, T], bool],
    accept: Callable[[T], bool],
) -> ViabilityCertificate:
    """Backward dynamic programming and lexicographically least viable path."""
    if not layers:
        raise ValueError("at least one layer is required")
    canon_layers = tuple(tuple(layer) for layer in layers)
    viable: list[set[T]] = [set() for _ in canon_layers]
    viable[-1] = {x for x in canon_layers[-1] if accept(x)}
    for i in range(len(canon_layers) - 2, -1, -1):
        viable[i] = {
            x
            for x in canon_layers[i]
            if any(edge(i, x, y) and y in viable[i + 1] for y in canon_layers[i + 1])
        }
    if not viable[0]:
        return ViabilityCertificate(canon_layers, tuple(frozenset(v) for v in viable), None)
    path: list[T] = [next(x for x in canon_layers[0] if x in viable[0])]
    for i in range(len(canon_layers) - 1):
        current = path[-1]
        nxt = next(
            y
            for y in canon_layers[i + 1]
            if y in viable[i + 1] and edge(i, current, y)
        )
        path.append(nxt)
    return ViabilityCertificate(canon_layers, tuple(frozenset(v) for v in viable), tuple(path))


def verify_viability(
    cert: ViabilityCertificate[T],
    edge: Callable[[int, T, T], bool],
    accept: Callable[[T], bool],
) -> bool:
    layers = cert.layers
    if len(layers) != len(cert.viable) or not layers:
        return False
    expected_last = frozenset(x for x in layers[-1] if accept(x))
    if cert.viable[-1] != expected_last:
        return False
    for i in range(len(layers) - 2, -1, -1):
        expected = frozenset(
            x
            for x in layers[i]
            if any(edge(i, x, y) and y in cert.viable[i + 1] for y in layers[i + 1])
        )
        if cert.viable[i] != expected:
            return False
    if cert.path is None:
        return not cert.viable[0]
    if len(cert.path) != len(layers):
        return False
    if cert.path[0] not in cert.viable[0] or not accept(cert.path[-1]):
        return False
    for i, (x, y) in enumerate(zip(cert.path, cert.path[1:])):
        if x not in layers[i] or y not in layers[i + 1] or not edge(i, x, y):
            return False
    return True


def observer_diameter(values: Sequence[Fraction]) -> Fraction:
    if not values:
        raise ValueError("at least one value is required")
    return max(values) - min(values)


def exact_observer_invariant(values: Sequence[Hashable]) -> bool:
    return bool(values) and all(v == values[0] for v in values)


@dataclass(frozen=True)
class TreeEdge:
    u: Hashable
    v: Hashable
    error: Fraction


def spanning_tree_distances(root: Hashable, edges: Sequence[TreeEdge]) -> dict[Hashable, Fraction]:
    """Accumulate certified metric errors along a finite tree."""
    graph: dict[Hashable, list[tuple[Hashable, Fraction]]] = {}
    for e in edges:
        if e.error < 0:
            raise ValueError("edge error must be nonnegative")
        graph.setdefault(e.u, []).append((e.v, e.error))
        graph.setdefault(e.v, []).append((e.u, e.error))
    if root not in graph and edges:
        raise ValueError("root is absent")
    dist: dict[Hashable, Fraction] = {root: Fraction(0)}
    queue: deque[Hashable] = deque([root])
    while queue:
        u = queue.popleft()
        for v, err in graph.get(u, []):
            if v not in dist:
                dist[v] = dist[u] + err
                queue.append(v)
    if len(dist) != len(graph) and graph:
        raise ValueError("edges do not form a connected graph")
    if edges and len(edges) != len(graph) - 1:
        raise ValueError("edges do not form a tree")
    return dist


def verify_metric_gluing(
    root: Hashable,
    values: Mapping[Hashable, Fraction],
    edges: Sequence[TreeEdge],
) -> bool:
    """Check edge inequalities and the induced root-to-vertex bounds."""
    distances = spanning_tree_distances(root, edges)
    if root not in values:
        return False
    for e in edges:
        if e.u not in values or e.v not in values:
            return False
        if abs(values[e.u] - values[e.v]) > e.error:
            return False
    return all(abs(values[v] - values[root]) <= d for v, d in distances.items())


def bounded_complete_list(bound: int, predicate: Callable[[int], bool]) -> list[int]:
    """Enumerate all witnesses below a supplied height bound."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return [x for x in range(bound + 1) if predicate(x)]


def verify_complete_list(
    bound: int,
    values: Sequence[int],
    predicate: Callable[[int], bool],
) -> bool:
    expected = bounded_complete_list(bound, predicate)
    return list(values) == expected


@dataclass(frozen=True)
class BisectionStep:
    lo: Fraction
    hi: Fraction
    mid: Fraction
    sign: int


@dataclass(frozen=True)
class CubicBisectionCertificate:
    x: Fraction
    initial_lo: Fraction
    initial_hi: Fraction
    steps: tuple[BisectionStep, ...]
    final_lo: Fraction
    final_hi: Fraction


def cubic_value(y: Fraction, x: Fraction) -> Fraction:
    return y * y * y + y - x


def _sign(q: Fraction) -> int:
    return (q > 0) - (q < 0)


def cubic_bisection(x: Fraction, lo: Fraction, hi: Fraction, fuel: int) -> CubicBisectionCertificate:
    """Exact bisection for y^3 + y = x on a certified bracket."""
    if fuel < 0:
        raise ValueError("fuel must be nonnegative")
    if not (cubic_value(lo, x) <= 0 <= cubic_value(hi, x)):
        raise ValueError("invalid bracket")
    initial_lo, initial_hi = lo, hi
    steps: list[BisectionStep] = []
    for _ in range(fuel):
        mid = (lo + hi) / 2
        s = _sign(cubic_value(mid, x))
        steps.append(BisectionStep(lo, hi, mid, s))
        if s <= 0:
            lo = mid
        else:
            hi = mid
    return CubicBisectionCertificate(x, initial_lo, initial_hi, tuple(steps), lo, hi)


def verify_cubic_bisection(cert: CubicBisectionCertificate) -> bool:
    lo, hi = cert.initial_lo, cert.initial_hi
    if cubic_value(lo, cert.x) > 0 or cubic_value(hi, cert.x) < 0:
        return False
    for step in cert.steps:
        if step.lo != lo or step.hi != hi or step.mid != (lo + hi) / 2:
            return False
        if step.sign != _sign(cubic_value(step.mid, cert.x)):
            return False
        if step.sign <= 0:
            lo = step.mid
        else:
            hi = step.mid
    return (
        lo == cert.final_lo
        and hi == cert.final_hi
        and cubic_value(lo, cert.x) <= 0 <= cubic_value(hi, cert.x)
        and hi - lo == (cert.initial_hi - cert.initial_lo) / (2 ** len(cert.steps))
    )


def enumerate_master_certificates(radices: Sequence[int]) -> Iterable[tuple[int, list[int]]]:
    """Enumerate the entire finite master-certificate space."""
    size = certificate_space_size(radices)
    for code in range(size):
        yield code, mixed_radix_decode(code, radices)
