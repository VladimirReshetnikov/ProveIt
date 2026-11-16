"""Reference algorithms for the finitary-interface framework.

This module is deliberately small and exact.  It is *not* an iPRA proof
checker and it is not a substitute for the Lean object-language development.
Its role is to make the finite algorithms, quantifier order, and certificate
formats executable and testable with Python's standard library.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from typing import Any, Callable, Generic, Iterable, Mapping, Sequence, TypeVar

T = TypeVar("T")


def _nat(n: int, name: str = "value") -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"{name} must be a natural number, got {n!r}")
    return n


def bounded_all(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Booleanization of ``forall i < bound``."""
    _nat(bound, "bound")
    return all(predicate(i) for i in range(bound))


def bounded_any(bound: int, predicate: Callable[[int], bool]) -> bool:
    """Booleanization of ``exists i < bound``."""
    _nat(bound, "bound")
    return any(predicate(i) for i in range(bound))


def bounded_least(
    bound: int, predicate: Callable[[int], bool], *, default: int | None = None
) -> int:
    """Least witness below ``bound``; optionally return ``default`` if absent."""
    _nat(bound, "bound")
    for i in range(bound):
        if predicate(i):
            return i
    if default is None:
        raise LookupError("no bounded witness")
    return default


def bounded_fold(bound: int, init: T, step: Callable[[int, T], T]) -> T:
    """The semantic counterpart of a primitive-recursive bounded fold."""
    _nat(bound, "bound")
    state = init
    for i in range(bound):
        state = step(i, state)
    return state


@dataclass(frozen=True)
class TraceSystem:
    """A one-input bounded trace with a local invariant and final contract."""

    good: Callable[[int], bool]
    init: Callable[[int], int]
    bound: Callable[[int], int]
    step: Callable[[int, int, int], int]
    invariant: Callable[[int, int, int], bool]
    accept: Callable[[int, int], bool]


def run_trace(system: TraceSystem, u: int) -> tuple[int, ...]:
    """Return all states, including the initial state."""
    _nat(u, "input")
    n = _nat(system.bound(u), "trace bound")
    states = [system.init(u)]
    for i in range(n):
        states.append(system.step(i, states[-1], u))
    return tuple(states)


def verify_trace(system: TraceSystem, u: int, states: Sequence[int]) -> bool:
    """Check the exact finite certificate used by trace reflection."""
    if not system.good(u):
        return False
    n = _nat(system.bound(u), "trace bound")
    if len(states) != n + 1 or states[0] != system.init(u):
        return False
    if not system.invariant(0, states[0], u):
        return False
    for i in range(n):
        if states[i + 1] != system.step(i, states[i], u):
            return False
        if not system.invariant(i + 1, states[i + 1], u):
            return False
    return system.accept(states[-1], u)


def trace_reflection_instance(system: TraceSystem, u: int) -> bool:
    """Finite semantic check of the theorem proved internally by qf induction."""
    if not system.good(u):
        return True
    return verify_trace(system, u, run_trace(system, u))


@dataclass(frozen=True)
class InterfaceNode:
    """One deterministic node of a static contract DAG.

    ``demand(q)`` returns one required precision for each dependency, in the
    same order as ``deps``.  ``compute`` and ``verify`` are finite semantic
    counterparts of the primitive-recursive symbol and its local contract.
    """

    name: str
    deps: tuple[str, ...]
    demand: Callable[[int], tuple[int, ...]]
    compute: Callable[[tuple[Any, ...], int], Any]
    verify: Callable[[tuple[Any, ...], int, Any], bool]


class ContractDAG:
    """Static, acyclic composition with a reverse demand pass."""

    def __init__(self, nodes: Sequence[InterfaceNode]):
        if not nodes:
            raise ValueError("a contract DAG needs at least one node")
        self._nodes = tuple(nodes)
        self._by_name: dict[str, InterfaceNode] = {}
        seen: set[str] = set()
        for node in self._nodes:
            if not node.name or node.name in seen:
                raise ValueError(f"duplicate or empty node name: {node.name!r}")
            missing = [d for d in node.deps if d not in seen]
            if missing:
                raise ValueError(
                    f"node {node.name!r} has non-earlier dependencies {missing!r}"
                )
            needs = node.demand(0)
            if len(needs) != len(node.deps):
                raise ValueError(f"demand arity mismatch at node {node.name!r}")
            if any((not isinstance(q, int) or q < 0) for q in needs):
                raise ValueError(f"negative/nonintegral demand at node {node.name!r}")
            seen.add(node.name)
            self._by_name[node.name] = node

    @property
    def names(self) -> tuple[str, ...]:
        return tuple(n.name for n in self._nodes)

    def reverse_demands(self, sink: str, precision: int) -> dict[str, int]:
        _nat(precision, "precision")
        if sink not in self._by_name:
            raise KeyError(sink)
        required: dict[str, int] = {name: 0 for name in self.names}
        active: set[str] = {sink}
        required[sink] = precision
        for node in reversed(self._nodes):
            if node.name not in active:
                continue
            q = required[node.name]
            needs = node.demand(q)
            if len(needs) != len(node.deps):
                raise ValueError(f"demand arity mismatch at node {node.name!r}")
            for dep, need in zip(node.deps, needs, strict=True):
                _nat(need, f"demand {node.name}->{dep}")
                required[dep] = max(required[dep], need)
                active.add(dep)
        return {name: required[name] for name in self.names if name in active}

    def execute(
        self,
        sink: str,
        precision: int,
        leaf_values: Mapping[str, Any] | None = None,
    ) -> tuple[Any, dict[str, Any], dict[str, int]]:
        """Execute the demanded sub-DAG and check each local contract."""
        leaf_values = dict(leaf_values or {})
        demands = self.reverse_demands(sink, precision)
        values: dict[str, Any] = {}
        for node in self._nodes:
            if node.name not in demands:
                continue
            q = demands[node.name]
            if not node.deps and node.name in leaf_values:
                value = leaf_values[node.name]
                args: tuple[Any, ...] = ()
            else:
                args = tuple(values[d] for d in node.deps)
                value = node.compute(args, q)
            if not node.verify(args, q, value):
                raise ValueError(f"local contract failed at node {node.name!r}")
            values[node.name] = value
        return values[sink], values, demands


@dataclass(frozen=True)
class FiniteRelationTower(Generic[T]):
    """Finite clouds connected by compatibility edges."""

    levels: tuple[tuple[T, ...], ...]
    edge: Callable[[int, T, T], bool]
    valid: Callable[[int, T], bool] = lambda _i, _x: True

    def __post_init__(self) -> None:
        if not self.levels:
            raise ValueError("tower must have at least one level")
        if any(not level for level in self.levels):
            raise ValueError("every level must be nonempty")

    @property
    def horizon(self) -> int:
        return len(self.levels) - 1

    def viability(self) -> tuple[frozenset[int], ...]:
        """Backward viability sets; all loops are bounded and finite."""
        h = self.horizon
        viable: list[set[int]] = [set() for _ in self.levels]
        viable[h] = {
            j for j, value in enumerate(self.levels[h]) if self.valid(h, value)
        }
        for i in range(h - 1, -1, -1):
            for j, value in enumerate(self.levels[i]):
                if not self.valid(i, value):
                    continue
                if any(
                    self.edge(i, value, self.levels[i + 1][k])
                    for k in viable[i + 1]
                ):
                    viable[i].add(j)
        return tuple(frozenset(v) for v in viable)

    def least_path(self) -> tuple[T, ...]:
        viable = self.viability()
        if not viable[0]:
            raise LookupError("there is no compatible full path")
        index = min(viable[0])
        path = [self.levels[0][index]]
        for i in range(self.horizon):
            next_index = min(
                k
                for k in viable[i + 1]
                if self.edge(i, path[-1], self.levels[i + 1][k])
            )
            path.append(self.levels[i + 1][next_index])
        return tuple(path)

    def all_paths(self) -> tuple[tuple[T, ...], ...]:
        paths: list[tuple[T, ...]] = []

        def visit(i: int, path: tuple[T, ...]) -> None:
            if i == self.horizon:
                paths.append(path)
                return
            for value in self.levels[i + 1]:
                if self.valid(i + 1, value) and self.edge(i, path[-1], value):
                    visit(i + 1, path + (value,))

        for value in self.levels[0]:
            if self.valid(0, value):
                visit(0, (value,))
        return tuple(paths)

    def terminal_observations(
        self, observe: Callable[[T], Any]
    ) -> tuple[Any, ...]:
        return tuple(observe(path[-1]) for path in self.all_paths())


class GuardResult(str, Enum):
    NEGATIVE = "negative"
    POSITIVE = "positive"
    UNRESOLVED = "unresolved"


def three_way_guard(center: Fraction, radius: Fraction) -> GuardResult:
    """A stable finite guard for a real known to lie in center +/- radius."""
    if radius < 0:
        raise ValueError("radius must be nonnegative")
    if center + radius < 0:
        return GuardResult.NEGATIVE
    if center - radius > 0:
        return GuardResult.POSITIVE
    return GuardResult.UNRESOLVED


@dataclass(frozen=True)
class RationalBall:
    center: Fraction
    radius: Fraction

    def __post_init__(self) -> None:
        if self.radius < 0:
            raise ValueError("radius must be nonnegative")

    def overlaps(self, other: "RationalBall") -> bool:
        return abs(self.center - other.center) <= self.radius + other.radius

    def contains(self, value: Fraction) -> bool:
        return abs(value - self.center) <= self.radius


def guarded_reciprocal(ball: RationalBall) -> RationalBall:
    """Reciprocal with an explicit positive separation from zero.

    For x in [c-r,c+r] not meeting zero, the midpoint 1/c has error at most
    r/(|c|(|c|-r)).  This is exact rational arithmetic.
    """
    c, r = ball.center, ball.radius
    if abs(c) <= r:
        raise ValueError("reciprocal requires a positive apartness margin")
    return RationalBall(Fraction(1, 1) / c, r / (abs(c) * (abs(c) - r)))


def cubic(z: Fraction) -> Fraction:
    return z * z * z + z


def _ceil_log2_fraction(x: Fraction) -> int:
    if x <= 1:
        return 0
    # Exact integer loop avoids floating-point dependence in certificates.
    k = 0
    p = Fraction(1)
    while p < x:
        p *= 2
        k += 1
    return k


def cubic_inverse_ball(x: Fraction, precision: int) -> RationalBall:
    """Regular-name approximation to the unique y with y^3 + y = x.

    The function z |-> z^3+z is strictly increasing.  Bisection starts from
    [-B,B], B=|x|+1, and takes enough exact rational steps that the returned
    radius is at most 2^(-precision-2).
    """
    _nat(precision, "precision")
    b = abs(x) + 1
    lo, hi = -b, b
    target_width = Fraction(1, 2 ** (precision + 1))
    steps = _ceil_log2_fraction((hi - lo) / target_width)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if cubic(mid) <= x:
            lo = mid
        else:
            hi = mid
    center = (lo + hi) / 2
    radius = (hi - lo) / 2
    return RationalBall(center, radius)


def cubic_inverse_certificate(x: Fraction, precision: int) -> dict[str, Any]:
    """Serializable bisection trace and invariant checks."""
    _nat(precision, "precision")
    b = abs(x) + 1
    lo, hi = -b, b
    target_width = Fraction(1, 2 ** (precision + 1))
    steps = _ceil_log2_fraction((hi - lo) / target_width)
    rows: list[dict[str, str]] = []
    for i in range(steps + 1):
        rows.append(
            {
                "i": str(i),
                "lo": str(lo),
                "hi": str(hi),
                "flo_minus_x": str(cubic(lo) - x),
                "fhi_minus_x": str(cubic(hi) - x),
                "width": str(hi - lo),
            }
        )
        if i == steps:
            break
        mid = (lo + hi) / 2
        if cubic(mid) <= x:
            lo = mid
        else:
            hi = mid
    ball = RationalBall((lo + hi) / 2, (hi - lo) / 2)
    return {
        "input": str(x),
        "precision": precision,
        "steps": steps,
        "ball": {"center": str(ball.center), "radius": str(ball.radius)},
        "trace": rows,
    }


def verify_cubic_inverse_certificate(cert: Mapping[str, Any]) -> bool:
    try:
        x = Fraction(str(cert["input"]))
        precision = _nat(int(cert["precision"]), "precision")
        rows = list(cert["trace"])
        steps = _nat(int(cert["steps"]), "steps")
        if len(rows) != steps + 1:
            return False
        last_lo: Fraction | None = None
        last_hi: Fraction | None = None
        for i, row in enumerate(rows):
            if int(row["i"]) != i:
                return False
            lo, hi = Fraction(row["lo"]), Fraction(row["hi"])
            if lo > hi or cubic(lo) > x or cubic(hi) < x:
                return False
            if Fraction(row["width"]) != hi - lo:
                return False
            if Fraction(row["flo_minus_x"]) != cubic(lo) - x:
                return False
            if Fraction(row["fhi_minus_x"]) != cubic(hi) - x:
                return False
            if last_lo is not None:
                if not (lo == last_lo or hi == last_hi):
                    return False
                if hi - lo != (last_hi - last_lo) / 2:
                    return False
            last_lo, last_hi = lo, hi
        assert last_lo is not None and last_hi is not None
        center = Fraction(cert["ball"]["center"])
        radius = Fraction(cert["ball"]["radius"])
        if center != (last_lo + last_hi) / 2 or radius != (last_hi - last_lo) / 2:
            return False
        return radius <= Fraction(1, 2 ** (precision + 2))
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False


def integer_points_from_height_bound(
    bound: int, predicate: Callable[[int], bool]
) -> tuple[int, ...]:
    """Complete integer list once an absolute-value height bound is supplied."""
    _nat(bound, "height bound")
    return tuple(z for z in range(-bound, bound + 1) if predicate(z))


def height_bound_from_complete_integer_list(
    points: Iterable[int], predicate: Callable[[int], bool]
) -> int:
    """The reverse finite-list-to-height direction for integer points."""
    materialized = tuple(points)
    if any(not predicate(z) for z in materialized):
        raise ValueError("the list contains a non-point")
    return max((abs(z) for z in materialized), default=0)


def finite_net_minimum(
    points: Sequence[T], value: Callable[[T], Fraction]
) -> tuple[T, Fraction]:
    """Least-index minimizer on a nonempty finite net."""
    if not points:
        raise ValueError("finite net must be nonempty")
    best_index = min(range(len(points)), key=lambda i: (value(points[i]), i))
    p = points[best_index]
    return p, value(p)


def fraction_to_json(x: Fraction) -> dict[str, int]:
    return {"numerator": x.numerator, "denominator": x.denominator}
