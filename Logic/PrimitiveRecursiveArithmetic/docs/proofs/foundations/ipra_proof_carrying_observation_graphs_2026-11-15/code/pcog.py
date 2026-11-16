"""Reference implementation for proof-carrying observation graphs (PCOGs).

This module is deliberately finite and exact.  It is *not* an iPRA proof
checker.  It mirrors the algorithms whose correctness contracts are intended
to be proved inside the deeply embedded ``Prf PRAAx`` calculus.

Only Python's standard library is used.  All analytic examples use
``fractions.Fraction``; no floating-point decision is trusted.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import prod
from typing import Any, Callable, Iterable, Mapping, Sequence


class ContractError(RuntimeError):
    """Raised when a finite certificate or graph contract fails."""


DemandMap = Mapping[str, int]
EvalFn = Callable[[Mapping[str, Any], int, Mapping[str, Any]], Any]
VerifyFn = Callable[[Mapping[str, Any], int, Any, Mapping[str, Any]], bool]
DemandFn = Callable[[int, Mapping[str, Any]], DemandMap]


@dataclass(frozen=True)
class Node:
    """One deterministic node in a fixed finite observation graph.

    ``dependencies`` is an ordered tuple of earlier node names.
    ``demand(q, parameters)`` returns the precision required from each
    dependency in order to answer at precision ``q``.
    ``evaluate(inputs, q, parameters)`` produces finite coded output.
    ``verify`` checks the node's local finite certificate.

    A mathematical formalization must replace each Python callable by a fixed
    primitive-recursive symbol and supply an object-iPRA proof of its local
    contract.  The Python object only exercises the staged architecture.
    """

    name: str
    dependencies: tuple[str, ...]
    demand: DemandFn
    evaluate: EvalFn
    verify: VerifyFn


@dataclass(frozen=True)
class GraphRun:
    requested: Mapping[str, int]
    demands: Mapping[str, int]
    outputs: Mapping[str, Any]


class ObservationGraph:
    """A fixed acyclic graph in topological order."""

    def __init__(self, nodes: Sequence[Node]) -> None:
        self.nodes = tuple(nodes)
        names = [node.name for node in self.nodes]
        if len(set(names)) != len(names):
            raise ValueError("node names must be unique")
        self._index = {name: i for i, name in enumerate(names)}
        for i, node in enumerate(self.nodes):
            for dep in node.dependencies:
                if dep not in self._index:
                    raise ValueError(f"unknown dependency {dep!r} of {node.name!r}")
                if self._index[dep] >= i:
                    raise ValueError(
                        f"dependency {dep!r} of {node.name!r} is not earlier"
                    )

    @property
    def names(self) -> tuple[str, ...]:
        return tuple(node.name for node in self.nodes)

    def backward_demands(
        self, requested: Mapping[str, int], parameters: Mapping[str, Any]
    ) -> dict[str, int]:
        """Compute least pointwise demands by one reverse topological pass."""

        demands = {name: 0 for name in self.names}
        for name, q in requested.items():
            if name not in self._index:
                raise KeyError(f"unknown requested output {name!r}")
            if q < 0:
                raise ValueError("precisions are natural numbers")
            demands[name] = max(demands[name], q)

        for node in reversed(self.nodes):
            q = demands[node.name]
            local = dict(node.demand(q, parameters))
            if set(local) - set(node.dependencies):
                extra = sorted(set(local) - set(node.dependencies))
                raise ContractError(
                    f"{node.name}: demand function mentioned nondependencies {extra}"
                )
            for dep in node.dependencies:
                d = int(local.get(dep, 0))
                if d < 0:
                    raise ContractError(
                        f"{node.name}: negative demand {d} for {dep}"
                    )
                demands[dep] = max(demands[dep], d)
        return demands

    def forward(
        self, demands: Mapping[str, int], parameters: Mapping[str, Any]
    ) -> dict[str, Any]:
        """Evaluate and locally verify nodes in topological order."""

        outputs: dict[str, Any] = {}
        for node in self.nodes:
            inputs = {dep: outputs[dep] for dep in node.dependencies}
            q = int(demands[node.name])
            out = node.evaluate(inputs, q, parameters)
            if not node.verify(inputs, q, out, parameters):
                raise ContractError(
                    f"local certificate failed at node {node.name!r}, precision {q}"
                )
            outputs[node.name] = out
        return outputs

    def run(
        self, requested: Mapping[str, int], parameters: Mapping[str, Any]
    ) -> GraphRun:
        demands = self.backward_demands(requested, parameters)
        outputs = self.forward(demands, parameters)
        return GraphRun(dict(requested), demands, outputs)


@dataclass(frozen=True, order=True)
class RationalInterval:
    """Closed rational interval used as a finite observation."""

    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("interval endpoints are reversed")

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    @property
    def midpoint(self) -> Fraction:
        return (self.lo + self.hi) / 2

    @property
    def radius(self) -> Fraction:
        return self.width / 2

    def contains(self, x: Fraction) -> bool:
        return self.lo <= x <= self.hi

    def reciprocal_positive(self) -> "RationalInterval":
        if self.lo <= 0:
            raise ContractError("positive reciprocal requires an apartness witness")
        return RationalInterval(1 / self.hi, 1 / self.lo)

    def add(self, other: "RationalInterval") -> "RationalInterval":
        return RationalInterval(self.lo + other.lo, self.hi + other.hi)

    def mul_nonnegative(self, other: "RationalInterval") -> "RationalInterval":
        if self.lo < 0 or other.lo < 0:
            raise ContractError("this finite multiplication rule expects nonnegative inputs")
        return RationalInterval(self.lo * other.lo, self.hi * other.hi)


def pow2_neg(p: int) -> Fraction:
    if p < 0:
        raise ValueError("precision must be nonnegative")
    return Fraction(1, 1 << p)


def cubic_value(y: Fraction) -> Fraction:
    return y * y * y + y


def cubic_bracket(x: Fraction, precision: int) -> RationalInterval:
    """Bisection bracket for the unique nonnegative root of y^3+y=x.

    The supplied example restricts ``0 <= x <= 2``.  The initial bracket
    [0, 1] is therefore valid, and exactly ``precision`` bisections give width
    ``2^-precision``.
    """

    if not (Fraction(0) <= x <= Fraction(2)):
        raise ValueError("example contract requires 0 <= x <= 2")
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(precision):
        mid = (lo + hi) / 2
        if cubic_value(mid) <= x:
            lo = mid
        else:
            hi = mid
    return RationalInterval(lo, hi)


def build_cubic_graph() -> ObservationGraph:
    """A small exact contract graph used by the regression suite.

    ``root`` produces a bracket for y^3+y=x.
    ``reciprocal`` consumes a stronger root bracket and is guarded by x>0.
    ``observable`` returns y+1/y as one interval.  The backward pass is visible:
    requesting p bits from ``observable`` asks for p+2a+5 bits from ``root``,
    where the supplied apartness exponent certifies x >= 2^-a.
    """

    def root_demand(q: int, _: Mapping[str, Any]) -> DemandMap:
        return {}

    def root_eval(
        _: Mapping[str, Any], q: int, parameters: Mapping[str, Any]
    ) -> RationalInterval:
        return cubic_bracket(Fraction(parameters["x"]), q)

    def root_verify(
        _: Mapping[str, Any], q: int, out: Any, parameters: Mapping[str, Any]
    ) -> bool:
        if not isinstance(out, RationalInterval):
            return False
        x = Fraction(parameters["x"])
        return (
            cubic_value(out.lo) <= x <= cubic_value(out.hi)
            and out.width <= pow2_neg(q)
            and out.lo >= 0
        )

    root = Node("root", (), root_demand, root_eval, root_verify)

    def recip_demand(q: int, parameters: Mapping[str, Any]) -> DemandMap:
        # From x >= 2^-a and y^3+y=x with 0<=y<=1 we get y >= 2^-(a+1).
        # If a root bracket has width 2^-n and n >= a+2, its lower endpoint
        # is at least 2^-(a+2).  Hence the reciprocal interval has width at
        # most 2^(2a+4-n).  Taking n=q+2a+4 makes this at most 2^-q.
        a = int(parameters.get("apartness_bits", 0))
        if a < 0:
            raise ContractError("apartness exponent must be nonnegative")
        return {"root": q + 2 * a + 4}

    def recip_eval(
        inputs: Mapping[str, Any], _: int, parameters: Mapping[str, Any]
    ) -> RationalInterval:
        x = Fraction(parameters["x"])
        a = int(parameters.get("apartness_bits", 0))
        if x < pow2_neg(a):
            raise ContractError("reciprocal node requires the certificate x >= 2^-a")
        root_interval = inputs["root"]
        assert isinstance(root_interval, RationalInterval)
        return root_interval.reciprocal_positive()

    def recip_verify(
        inputs: Mapping[str, Any], q: int, out: Any, parameters: Mapping[str, Any]
    ) -> bool:
        x = Fraction(parameters["x"])
        a = int(parameters.get("apartness_bits", 0))
        if x < pow2_neg(a):
            return False
        r = inputs["root"]
        if not isinstance(r, RationalInterval) or not isinstance(out, RationalInterval):
            return False
        return (
            r.lo > 0
            and out == RationalInterval(1 / r.hi, 1 / r.lo)
            and out.width <= pow2_neg(q)
        )

    reciprocal = Node(
        "reciprocal", ("root",), recip_demand, recip_eval, recip_verify
    )

    def obs_demand(q: int, _: Mapping[str, Any]) -> DemandMap:
        # Split the output-width budget equally between the root and reciprocal
        # intervals.  The reciprocal node propagates its apartness-dependent
        # demand farther back to the root node.
        return {"root": q + 1, "reciprocal": q + 1}

    def obs_eval(
        inputs: Mapping[str, Any], _: int, __: Mapping[str, Any]
    ) -> RationalInterval:
        r = inputs["root"]
        inv = inputs["reciprocal"]
        assert isinstance(r, RationalInterval)
        assert isinstance(inv, RationalInterval)
        return r.add(inv)

    def obs_verify(
        inputs: Mapping[str, Any], q: int, out: Any, __: Mapping[str, Any]
    ) -> bool:
        r = inputs["root"]
        inv = inputs["reciprocal"]
        return (
            isinstance(r, RationalInterval)
            and isinstance(inv, RationalInterval)
            and isinstance(out, RationalInterval)
            and out == r.add(inv)
            and out.width <= pow2_neg(q)
        )

    observable = Node(
        "observable", ("root", "reciprocal"), obs_demand, obs_eval, obs_verify
    )
    return ObservationGraph([root, reciprocal, observable])


def all_below(bound: int, predicate: Callable[[int], bool]) -> bool:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return all(predicate(i) for i in range(bound))


def any_below(bound: int, predicate: Callable[[int], bool]) -> bool:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return any(predicate(i) for i in range(bound))


def least_below(bound: int, predicate: Callable[[int], bool]) -> int | None:
    """Least witness in [0,bound), or None.  This is a bounded PR search."""

    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(bound):
        if predicate(i):
            return i
    return None


Compatibility = Callable[[int, Any, Any], bool]
Validity = Callable[[int, Any], bool]


@dataclass(frozen=True)
class ViabilityResult:
    viable: tuple[tuple[bool, ...], ...]
    path: tuple[int, ...]


def backward_viability(
    clouds: Sequence[Sequence[Any]],
    compatible: Compatibility,
    valid: Validity | None = None,
) -> tuple[tuple[bool, ...], ...]:
    """Backward dynamic program for a finite relational presentation."""

    if not clouds:
        return ()
    if valid is None:
        valid = lambda _level, _candidate: True
    viable: list[list[bool]] = [
        [False for _ in cloud] for cloud in clouds
    ]
    last = len(clouds) - 1
    for a, candidate in enumerate(clouds[last]):
        viable[last][a] = bool(valid(last, candidate))
    for level in range(last - 1, -1, -1):
        for a, candidate in enumerate(clouds[level]):
            viable[level][a] = bool(valid(level, candidate)) and any(
                viable[level + 1][b]
                and compatible(level, candidate, next_candidate)
                for b, next_candidate in enumerate(clouds[level + 1])
            )
    return tuple(tuple(row) for row in viable)


def least_viable_path(
    clouds: Sequence[Sequence[Any]],
    compatible: Compatibility,
    valid: Validity | None = None,
) -> ViabilityResult:
    """Return the lexicographically least viable path.

    The construction is bounded search over finite clouds, not countable or
    dependent choice.  It fails explicitly when no full path exists.
    """

    viability = backward_viability(clouds, compatible, valid)
    if not clouds:
        return ViabilityResult(viability, ())
    starts = [i for i, ok in enumerate(viability[0]) if ok]
    if not starts:
        raise ContractError("the relational presentation has no full finite path")
    path = [starts[0]]
    for level in range(len(clouds) - 1):
        current = clouds[level][path[-1]]
        candidates = [
            b
            for b, nxt in enumerate(clouds[level + 1])
            if viability[level + 1][b]
            and compatible(level, current, nxt)
        ]
        if not candidates:
            raise AssertionError("viability invariant was violated")
        path.append(candidates[0])
    return ViabilityResult(viability, tuple(path))


def finite_horizon_paths(
    clouds: Sequence[Sequence[Any]],
    compatible: Compatibility,
    valid: Validity | None = None,
) -> tuple[tuple[int, ...], ...]:
    """Least path for every nonempty prefix of a cloud tower."""

    return tuple(
        least_viable_path(clouds[:h], compatible, valid).path
        for h in range(1, len(clouds) + 1)
    )


def maximum_diameter(
    values: Iterable[Any], distance: Callable[[Any, Any], Fraction]
) -> Fraction:
    values = tuple(values)
    if not values:
        return Fraction(0)
    return max(distance(a, b) for a in values for b in values)


def coherence_bounds_from_horizon_paths(
    clouds: Sequence[Sequence[Any]],
    paths: Sequence[Sequence[int]],
    observe: Callable[[int, Any], Fraction],
) -> tuple[Fraction, ...]:
    """Observed changes for the diagonal finite-horizon selection.

    The n-th selected value is level n of the least path through horizon n+1.
    This is the finite object used in the shrinking-viability theorem.
    """

    selected = [
        observe(level, clouds[level][paths[level][level]])
        for level in range(len(paths))
    ]
    return tuple(abs(selected[i + 1] - selected[i]) for i in range(len(selected) - 1))


def stable_label(
    interval: RationalInterval,
    labels: Sequence[Fraction],
    separation: Fraction,
) -> Fraction:
    """Collapse an approximate observation to a unique separated label.

    The theorem-level precondition is ``interval.width < separation`` and the
    existence of a label in the interval.  Pairwise separation then makes the
    label unique.  Without the explicit gap the function refuses to decide.
    """

    if separation <= 0:
        raise ContractError("a positive separation witness is required")
    if interval.width >= separation:
        raise ContractError("observation is not sharp enough for exact collapse")
    inside = [label for label in labels if interval.contains(label)]
    if len(inside) != 1:
        raise ContractError(
            f"expected exactly one separated label, found {len(inside)}"
        )
    for i, a in enumerate(labels):
        for b in labels[i + 1 :]:
            if abs(a - b) < separation:
                raise ContractError("the supplied label separation is false")
    return inside[0]


def complete_height_list(
    bound: int,
    universe: Iterable[Any],
    height: Callable[[Any], int],
    predicate: Callable[[Any], bool],
) -> tuple[Any, ...]:
    """Filter an explicit bounded enumeration into a complete list."""

    if bound < 0:
        raise ValueError("height bound must be nonnegative")
    out = []
    for value in universe:
        h = height(value)
        if h < 0:
            raise ContractError("height must be natural-valued")
        if h <= bound and predicate(value):
            out.append(value)
    return tuple(out)


def list_height_bound(values: Iterable[Any], height: Callable[[Any], int]) -> int:
    values = tuple(values)
    return max((height(value) for value in values), default=0)


def common_good_index(
    length: int,
    bad_predicates: Sequence[Callable[[int], bool]],
    budgets: Sequence[int],
) -> int:
    """Find a point outside a finite union of exceptional sets.

    Each budget is checked rather than trusted.  If ``length`` exceeds their
    sum, the elementary union bound guarantees success.
    """

    if length < 0 or len(bad_predicates) != len(budgets):
        raise ValueError("malformed finite-window instance")
    actual = [sum(1 for i in range(length) if bad(i)) for bad in bad_predicates]
    if any(a > b for a, b in zip(actual, budgets, strict=True)):
        raise ContractError(f"an exceptional-set budget is false: {actual} > {budgets}")
    if length <= sum(budgets):
        raise ContractError("the union bound does not force a common good index")
    witness = least_below(length, lambda i: not any(bad(i) for bad in bad_predicates))
    if witness is None:
        raise AssertionError("verified union bound failed")
    return witness


def mixed_radix_rank(coords: Sequence[int], bounds: Sequence[int]) -> int:
    """Rank a bounded tuple in lexicographic mixed radix (leftmost major)."""

    if len(coords) != len(bounds):
        raise ValueError("coordinate and bound dimensions differ")
    if any(b < 0 for b in bounds):
        raise ValueError("bounds must be natural numbers")
    if any(c < 0 or c > b for c, b in zip(coords, bounds, strict=True)):
        raise ContractError("coordinate lies outside its certified envelope")
    rank = 0
    for c, b in zip(coords, bounds, strict=True):
        rank = rank * (b + 1) + c
    return rank


def lex_decreases(
    before: Sequence[int], after: Sequence[int], bounds: Sequence[int]
) -> bool:
    """Check strict lexicographic decrease and its mixed-radix consequence."""

    if len(before) != len(after):
        return False
    lex = tuple(after) < tuple(before)
    return lex and mixed_radix_rank(after, bounds) < mixed_radix_rank(before, bounds)


def bounded_chain_fuel(bounds: Sequence[int]) -> int:
    """Number of possible bounded rank values; a strict descent is shorter."""

    if any(b < 0 for b in bounds):
        raise ValueError("bounds must be nonnegative")
    return prod(b + 1 for b in bounds)


def rational_pairs(bound: int) -> tuple[Fraction, ...]:
    """A duplicate-free enumeration of rationals with bounded numerator/denominator."""

    values = {
        Fraction(num, den)
        for den in range(1, bound + 1)
        for num in range(-bound, bound + 1)
    }
    return tuple(sorted(values))


def rational_height(q: Fraction) -> int:
    return max(abs(q.numerator), q.denominator)


def telescope(values: Sequence[Fraction]) -> Fraction:
    if len(values) < 2:
        return Fraction(0)
    return sum((abs(b - a) for a, b in zip(values, values[1:], strict=True)), Fraction(0))
