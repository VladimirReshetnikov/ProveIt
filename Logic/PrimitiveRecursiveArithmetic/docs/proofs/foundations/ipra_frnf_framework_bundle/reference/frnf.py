"""Exact reference algorithms for the Finitary Realizer Normal Form (FRNF).

This module is not a proof of iPRA soundness.  It is an executable model of the
finite algorithms whose object-language correctness proofs are specified in the
paper and Lean blueprints:

* bounded least search;
* dual computation/justification horizon composition;
* reverse demand closure on a finite acyclic graph;
* backward viability and canonical finite-path selection;
* majorized (fuelled) descent;
* finite-net minimization and stable exact collapse.

Only Python's standard library is used.  Fractions are exact.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Generic, Hashable, Iterable, Mapping, Sequence, TypeVar

T = TypeVar("T")
U = TypeVar("U")


def bounded_least(predicate: Callable[[int], bool], bound: int) -> int:
    """Return the least i < bound satisfying predicate, or bound if none exists."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(bound):
        if predicate(i):
            return i
    return bound


def prefix_max(f: Callable[[int], int], bound: int) -> int:
    """max(f(q) for q <= bound), with validation of natural-number outputs."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    values = [f(q) for q in range(bound + 1)]
    if any(v < 0 for v in values):
        raise ValueError("horizon functions must return natural numbers")
    return max(values, default=0)


@dataclass(frozen=True)
class DualHorizon:
    """Computation and proof horizons for one finite-use interface.

    read(d) is the largest input row needed to compute output row d.
    justify(d) is the largest input contract row needed to prove that output
    row d is valid.  Sound interfaces satisfy read(d) <= justify(d).
    """

    read: Callable[[int], int]
    justify: Callable[[int], int]
    name: str = "interface"

    def check(self, through: int) -> None:
        if through < 0:
            raise ValueError("through must be nonnegative")
        previous_read = -1
        previous_justify = -1
        for d in range(through + 1):
            r = self.read(d)
            j = self.justify(d)
            if r < 0 or j < 0:
                raise ValueError(f"{self.name}: negative horizon at {d}")
            if r > j:
                raise ValueError(
                    f"{self.name}: read horizon {r} exceeds justification horizon {j} at {d}"
                )
            if r < previous_read or j < previous_justify:
                raise ValueError(f"{self.name}: horizons are not monotone at {d}")
            previous_read, previous_justify = r, j

    def then(self, outer: "DualHorizon", *, name: str | None = None) -> "DualHorizon":
        """Compose self : X -> Y with outer : Y -> Z.

        Prefix maxima make the formula correct even when a transducer requests
        several rows below its nominal horizon.  For monotone functions this
        simplifies to ordinary function composition.
        """

        return DualHorizon(
            read=lambda d: prefix_max(self.read, outer.read(d)),
            justify=lambda d: prefix_max(self.justify, outer.justify(d)),
            name=name or f"{outer.name}∘{self.name}",
        )


@dataclass(frozen=True)
class EdgeDemand:
    """How a node's demanded output rows propagate to one dependency."""

    dependency: str
    horizon: DualHorizon


@dataclass(frozen=True)
class DemandNode:
    name: str
    dependencies: tuple[EdgeDemand, ...] = ()


@dataclass(frozen=True)
class DemandPair:
    read: int = 0
    justify: int = 0

    def join(self, other: "DemandPair") -> "DemandPair":
        return DemandPair(max(self.read, other.read), max(self.justify, other.justify))


def reverse_demand_closure(
    nodes_in_topological_order: Sequence[DemandNode],
    root: str,
    demand: int,
) -> dict[str, DemandPair | None]:
    """Compute least read/justification demands on the root dependency cone.

    ``None`` means that a node is not demanded at all.  This bottom element is
    essential: numerical demand 0 means "row 0 is required", not "unused".
    The input order must list dependencies before their users.  A single
    reverse pass suffices because the graph is acyclic.
    """
    if demand < 0:
        raise ValueError("demand must be nonnegative")
    by_name = {node.name: node for node in nodes_in_topological_order}
    if len(by_name) != len(nodes_in_topological_order):
        raise ValueError("node names must be unique")
    if root not in by_name:
        raise KeyError(root)

    position = {node.name: i for i, node in enumerate(nodes_in_topological_order)}
    for node in nodes_in_topological_order:
        for edge in node.dependencies:
            if edge.dependency not in by_name:
                raise KeyError(f"unknown dependency {edge.dependency!r}")
            if position[edge.dependency] >= position[node.name]:
                raise ValueError("order is not topological")

    demands: dict[str, DemandPair | None] = {
        node.name: None for node in nodes_in_topological_order
    }
    demands[root] = DemandPair(demand, demand)

    for node in reversed(nodes_in_topological_order):
        current = demands[node.name]
        if current is None:
            continue
        for edge in node.dependencies:
            propagated = DemandPair(
                read=prefix_max(edge.horizon.read, current.read),
                justify=prefix_max(edge.horizon.justify, current.justify),
            )
            if propagated.read > propagated.justify:
                raise ValueError(
                    f"edge {node.name}->{edge.dependency} violates read <= justify"
                )
            old = demands[edge.dependency]
            demands[edge.dependency] = (
                propagated if old is None else old.join(propagated)
            )
    return demands


@dataclass(frozen=True)
class Layer(Generic[T]):
    candidates: tuple[T, ...]

    @classmethod
    def from_iterable(cls, values: Iterable[T]) -> "Layer[T]":
        return cls(tuple(values))


@dataclass(frozen=True)
class ViabilityResult(Generic[T]):
    viable: tuple[frozenset[int], ...]
    path_indices: tuple[int, ...]
    path: tuple[T, ...]


def backward_viability(
    layers: Sequence[Layer[T]],
    compatible: Callable[[int, T, T], bool],
) -> ViabilityResult[T]:
    """Prune dead ends and select the lexicographically least viable path.

    compatible(i, a, b) relates level i to level i+1.  Empty input or a graph
    with no complete path raises ValueError.
    """
    if not layers:
        raise ValueError("at least one layer is required")
    if any(not layer.candidates for layer in layers):
        raise ValueError("every layer must have at least one candidate")

    viable: list[set[int]] = [set() for _ in layers]
    viable[-1] = set(range(len(layers[-1].candidates)))

    for i in range(len(layers) - 2, -1, -1):
        for a_idx, a in enumerate(layers[i].candidates):
            if any(
                compatible(i, a, layers[i + 1].candidates[b_idx])
                for b_idx in viable[i + 1]
            ):
                viable[i].add(a_idx)

    if not viable[0]:
        raise ValueError("no complete compatible path exists")

    path_indices = [min(viable[0])]
    for i in range(len(layers) - 1):
        a = layers[i].candidates[path_indices[-1]]
        options = [
            b_idx
            for b_idx in viable[i + 1]
            if compatible(i, a, layers[i + 1].candidates[b_idx])
        ]
        if not options:
            raise AssertionError("viability invariant was broken")
        path_indices.append(min(options))

    path = tuple(layer.candidates[index] for layer, index in zip(layers, path_indices))
    return ViabilityResult(
        viable=tuple(frozenset(v) for v in viable),
        path_indices=tuple(path_indices),
        path=path,
    )


def majorized_run(
    state: T,
    step: Callable[[T], T],
    terminal: Callable[[T], bool],
    rank: Callable[[T], int],
) -> tuple[T, tuple[T, ...]]:
    """Run a frozen descent for rank(initial)+1 stages and audit each decrease."""
    initial_rank = rank(state)
    if initial_rank < 0:
        raise ValueError("rank must be natural-valued")
    trace = [state]
    for _ in range(initial_rank + 1):
        if terminal(state):
            next_state = state
        else:
            next_state = step(state)
            if rank(next_state) >= rank(state):
                raise ValueError("nonterminal step did not strictly decrease rank")
        state = next_state
        trace.append(state)
    if not terminal(state):
        raise ValueError("rank argument did not establish termination")
    return state, tuple(trace)


def euclid_majorized(a: int, b: int) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Euclidean gcd as a majorized loop, mirroring the iPRA construction."""
    if a < 0 or b < 0:
        raise ValueError("inputs must be natural numbers")

    final, trace = majorized_run(
        (a, b),
        step=lambda s: (s[1], s[0] % s[1]),
        terminal=lambda s: s[1] == 0,
        rank=lambda s: s[1],
    )
    return final[0], trace


@dataclass(frozen=True)
class FiniteNetResult(Generic[T]):
    index: int
    point: T
    value: Fraction


def finite_net_minimum(
    points: Sequence[T], evaluator: Callable[[T], Fraction]
) -> FiniteNetResult[T]:
    """Least-index exact minimum on a nonempty finite net."""
    if not points:
        raise ValueError("finite net must be nonempty")
    values = [evaluator(point) for point in points]
    best_value = min(values)
    best_index = values.index(best_value)
    return FiniteNetResult(best_index, points[best_index], best_value)


def diameter(values: Sequence[Fraction]) -> Fraction:
    if not values:
        raise ValueError("diameter of empty set is undefined")
    return max(values) - min(values)


def stable_observation(
    values: Sequence[Fraction], tolerance: Fraction
) -> Fraction:
    """Select an arbitrary canonical representative after checking stability."""
    if tolerance < 0:
        raise ValueError("tolerance must be nonnegative")
    if diameter(values) > tolerance:
        raise ValueError("candidate cloud is not stable at the requested tolerance")
    return values[0]


def exact_label_from_gap(
    approximations: Sequence[Fraction],
    labels: Sequence[U],
    separation: Fraction,
    error: Fraction,
) -> U:
    """Collapse a candidate cloud to an exact discrete label under a gap.

    The routine checks a simple sufficient condition: all approximations lie
    within 2*error of the first, and 2*error < separation.  In a formal use,
    separation is a certified lower bound between distinct labels' observables.
    """
    if len(approximations) != len(labels) or not labels:
        raise ValueError("approximations and labels must be equally nonempty")
    if separation <= 0 or error < 0:
        raise ValueError("invalid separation/error")
    if 2 * error >= separation:
        raise ValueError("error is too large for exact collapse")
    first = approximations[0]
    if any(abs(value - first) > 2 * error for value in approximations[1:]):
        raise ValueError("approximations do not identify a single separated class")
    if any(label != labels[0] for label in labels[1:]):
        raise ValueError("supplied labels disagree despite claimed exact collapse")
    return labels[0]


def guarded_reciprocal_error(input_error: Fraction, lower_bound: Fraction) -> Fraction:
    """Error bound |1/x-1/q| <= 2*eps/lambda^2 under |x|,|q| >= lambda/2."""
    if input_error < 0:
        raise ValueError("input error must be nonnegative")
    if lower_bound <= 0:
        raise ValueError("a positive apartness bound is required")
    return 2 * input_error / (lower_bound * lower_bound)
