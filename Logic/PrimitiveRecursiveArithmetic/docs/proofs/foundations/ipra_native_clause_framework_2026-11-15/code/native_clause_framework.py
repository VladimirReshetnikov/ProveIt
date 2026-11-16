"""Exact finite reference algorithms for the Native Clause Framework.

This module is not an iPRA proof checker.  It implements the finite algorithms
whose totality and correctness are proved in the accompanying report and whose
object-language compilation is outlined in Lean.

Only the Python standard library is used.  Quantitative examples use
``fractions.Fraction`` so that no floating-point evidence is mistaken for an
exact certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Hashable, Iterable, Mapping, Sequence


Demand = tuple[int, ...]


def componentwise_max(a: Demand, b: Demand) -> Demand:
    """Join in a finite product of chains."""
    if len(a) != len(b):
        raise ValueError("demand vectors must have the same dimension")
    return tuple(max(x, y) for x, y in zip(a, b, strict=True))


def leq(a: Demand, b: Demand) -> bool:
    if len(a) != len(b):
        raise ValueError("demand vectors must have the same dimension")
    return all(x <= y for x, y in zip(a, b, strict=True))


def bounded_monotone_closure(
    bounds: Demand,
    transformer: Callable[[Demand], Demand],
    start: Demand | None = None,
) -> tuple[Demand, list[Demand]]:
    """Compute the least prefixed point above ``start``.

    The iteration is x_{t+1} = x_t join F(x_t).  The function checks that the
    transformer remains in the finite box and is inflationary after joining.
    Under monotonicity (a mathematical contract checked separately), the result
    is the least prefixed point.  Termination needs at most sum(bounds) rank
    increases from zero; starting above zero only decreases this bound.
    """
    if any(b < 0 for b in bounds):
        raise ValueError("bounds must be nonnegative")
    current = start if start is not None else tuple(0 for _ in bounds)
    if len(current) != len(bounds) or not leq(current, bounds):
        raise ValueError("start must lie in the finite box")

    history = [current]
    # One final step is allowed to witness that a fixed point has been reached.
    max_steps = sum(bounds) - sum(current) + 1
    for _ in range(max_steps):
        image = transformer(current)
        if len(image) != len(bounds) or not leq(image, bounds):
            raise ValueError("transformer left the finite box")
        nxt = componentwise_max(current, image)
        history.append(nxt)
        if nxt == current:
            return current, history
        if sum(nxt) <= sum(current):
            raise AssertionError("a strict product-order increase must raise rank")
        current = nxt
    raise AssertionError("finite-rank termination bound was violated")


def check_monotone_on_box(
    bounds: Demand, transformer: Callable[[Demand], Demand]
) -> bool:
    """Exhaustively check monotonicity for small finite boxes."""
    points: list[Demand] = [()]
    for b in bounds:
        points = [p + (x,) for p in points for x in range(b + 1)]
    for x in points:
        fx = transformer(x)
        for y in points:
            if leq(x, y) and not leq(fx, transformer(y)):
                return False
    return True


@dataclass(frozen=True)
class DemandNode:
    """One node of an acyclic backward-demand graph.

    ``pullback`` maps an output demand to demands on named predecessors.
    Every returned predecessor must occur earlier in the topological order.
    """

    name: str
    predecessors: tuple[str, ...]
    pullback: Callable[[Demand], Mapping[str, Demand]]


def backward_demands(
    nodes: Sequence[DemandNode], goal: str, goal_demand: Demand
) -> dict[str, Demand]:
    """Compute least demands by one reverse topological pass."""
    position = {node.name: i for i, node in enumerate(nodes)}
    if len(position) != len(nodes):
        raise ValueError("node names must be unique")
    if goal not in position:
        raise KeyError(goal)
    dimension = len(goal_demand)
    zero = tuple(0 for _ in range(dimension))
    demand = {node.name: zero for node in nodes}
    demand[goal] = goal_demand

    for i in range(position[goal], -1, -1):
        node = nodes[i]
        pulled = node.pullback(demand[node.name])
        if set(pulled) - set(node.predecessors):
            raise ValueError(f"{node.name}: pullback mentioned a non-predecessor")
        for pred in node.predecessors:
            if position[pred] >= i:
                raise ValueError("nodes are not in topological order")
            req = pulled.get(pred, zero)
            if len(req) != dimension or any(x < 0 for x in req):
                raise ValueError("invalid predecessor demand")
            demand[pred] = componentwise_max(demand[pred], req)
    return demand


@dataclass(frozen=True)
class TraceResult:
    states: tuple[Any, ...]
    invariant_holds: bool


def verified_trace(
    initial: Any,
    step: Callable[[int, Any], Any],
    invariant: Callable[[int, Any], bool],
    fuel: int,
) -> TraceResult:
    """Run a clocked finite trace and check its invariant at every time."""
    if fuel < 0:
        raise ValueError("fuel must be nonnegative")
    states = [initial]
    ok = invariant(0, initial)
    state = initial
    for t in range(fuel):
        state = step(t, state)
        states.append(state)
        ok = ok and invariant(t + 1, state)
    return TraceResult(tuple(states), ok)


def bounded_least(bound: int, predicate: Callable[[int], bool]) -> int | None:
    """Least witness in [0,bound], or None when there is no witness."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for x in range(bound + 1):
        if predicate(x):
            return x
    return None


def bounded_enumeration(bound: int, predicate: Callable[[int], bool]) -> tuple[int, ...]:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return tuple(x for x in range(bound + 1) if predicate(x))


@dataclass(frozen=True)
class ViabilityResult:
    viable: tuple[frozenset[Hashable], ...]
    least_path: tuple[Hashable, ...] | None


def relational_viability(
    layers: Sequence[Sequence[Hashable]],
    edge: Callable[[int, Hashable, Hashable], bool],
    good: Callable[[int, Hashable], bool] | None = None,
    key: Callable[[Hashable], Any] | None = None,
) -> ViabilityResult:
    """Backward viability and the lexicographically least viable path."""
    if not layers:
        raise ValueError("at least one layer is required")
    good_fn = good or (lambda _q, _w: True)
    order_key = key or (lambda x: x)

    viable: list[set[Hashable]] = [set() for _ in layers]
    last = len(layers) - 1
    viable[last] = {w for w in layers[last] if good_fn(last, w)}
    for q in range(last - 1, -1, -1):
        viable[q] = {
            w
            for w in layers[q]
            if good_fn(q, w)
            and any(edge(q, w, v) for v in viable[q + 1])
        }

    frozen = tuple(frozenset(v) for v in viable)
    if not viable[0]:
        return ViabilityResult(frozen, None)

    path: list[Hashable] = [min(viable[0], key=order_key)]
    for q in range(last):
        candidates = [v for v in viable[q + 1] if edge(q, path[-1], v)]
        if not candidates:
            raise AssertionError("backward viability promised a successor")
        path.append(min(candidates, key=order_key))
    return ViabilityResult(frozen, tuple(path))


def max_pairwise_distance(
    values: Sequence[Any], distance: Callable[[Any, Any], Fraction]
) -> Fraction:
    diameter = Fraction(0)
    for i, x in enumerate(values):
        for y in values[i + 1 :]:
            d = distance(x, y)
            if d < 0:
                raise ValueError("distance must be nonnegative")
            diameter = max(diameter, d)
    return diameter


def stable_observation(
    witnesses: Iterable[Hashable],
    observer: Callable[[Hashable], Any],
    distance: Callable[[Any, Any], Fraction],
    tolerance: Fraction,
) -> tuple[Any, Fraction]:
    """Return a representative observation after checking branch diameter."""
    ws = tuple(witnesses)
    if not ws:
        raise ValueError("a stable observation needs at least one witness")
    if tolerance < 0:
        raise ValueError("tolerance must be nonnegative")
    values = tuple(observer(w) for w in ws)
    diameter = max_pairwise_distance(values, distance)
    if diameter > tolerance:
        raise ValueError("observer is not stable at the requested tolerance")
    return values[0], diameter


def tail_bound(motion: Sequence[Fraction], start: int) -> Fraction:
    if not 0 <= start <= len(motion):
        raise ValueError("invalid tail start")
    if any(x < 0 for x in motion):
        raise ValueError("motion bounds must be nonnegative")
    return sum(motion[start:], Fraction(0))


def exact_label_from_gap(
    approximation: Fraction,
    labels: Sequence[Fraction],
    error: Fraction,
    separation: Fraction,
) -> int:
    """Recover a unique exact label from a certified approximation.

    The contract is ``2*error < separation`` and pairwise label separation at
    least ``separation``.  The returned index is the unique label within error.
    """
    if error < 0 or separation <= 0 or 2 * error >= separation:
        raise ValueError("need 2*error < separation")
    for i, x in enumerate(labels):
        for y in labels[i + 1 :]:
            if abs(x - y) < separation:
                raise ValueError("labels violate the separation certificate")
    candidates = [i for i, x in enumerate(labels) if abs(approximation - x) <= error]
    if len(candidates) != 1:
        raise ValueError("certificate does not isolate exactly one label")
    return candidates[0]


def list_from_height(height: int, predicate: Callable[[int], bool]) -> tuple[int, ...]:
    """Complete list of coded objects under an explicit code-height bound."""
    return bounded_enumeration(height, predicate)


def height_from_complete_list(values: Sequence[int]) -> int:
    """A complete finite list supplies a code-height bound (0 for empty)."""
    if any(v < 0 for v in values):
        raise ValueError("codes must be natural numbers")
    return max(values, default=0)


def common_good_window(
    start: int,
    forbidden: Sequence[set[int]],
) -> int:
    """Find a point outside finitely many finite exceptional sets.

    If every set has at most b_i elements, a window of length
    1 + sum_i b_i must contain a common good point.  Here the exact finite sets
    are supplied, so their cardinalities provide the bound.
    """
    if start < 0:
        raise ValueError("start must be nonnegative")
    length = 1 + sum(len(s) for s in forbidden)
    for n in range(start, start + length):
        if all(n not in s for s in forbidden):
            return n
    raise AssertionError("finite union bound was violated")


def finite_descent_fuel(bounds: Demand) -> int:
    """Fuel for strict descent in a fixed-dimensional lexicographic box."""
    if any(b < 0 for b in bounds):
        raise ValueError("bounds must be nonnegative")
    fuel = 1
    for b in bounds:
        fuel *= b + 1
    return fuel


def check_strict_lex_descent(states: Sequence[Demand]) -> bool:
    """Check strict lexicographic descent of a finite state sequence."""
    return all(a > b for a, b in zip(states, states[1:]))


@dataclass(frozen=True)
class ContractNode:
    """Executable analogue of one proof-carrying node.

    ``checker`` is a finite verifier for the node's output.  In the formal
    framework a node additionally carries a KPrf derivation; this executable
    class deliberately does not pretend that a successful Python checker is
    such a derivation.
    """

    name: str
    predecessors: tuple[str, ...]
    evaluate: Callable[[Mapping[str, Any]], Any]
    checker: Callable[[Mapping[str, Any], Any], bool]


def execute_contract_graph(nodes: Sequence[ContractNode]) -> dict[str, Any]:
    values: dict[str, Any] = {}
    for node in nodes:
        missing = [p for p in node.predecessors if p not in values]
        if missing:
            raise ValueError(f"{node.name}: missing predecessors {missing}")
        env = {p: values[p] for p in node.predecessors}
        value = node.evaluate(env)
        if not node.checker(env, value):
            raise ValueError(f"{node.name}: local certificate failed")
        values[node.name] = value
    return values
