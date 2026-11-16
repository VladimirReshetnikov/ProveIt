"""Finite reference algorithms for the CIFER iPRA framework.

This module is deliberately small and exact.  It is not a proof checker for
intuitionistic primitive recursive arithmetic.  It implements the finite host
algorithms whose object-language correctness proofs are specified in the
paper and Lean plan:

* dependency-normal residual extraction on a fixed proof DAG;
* capped monotone demand closure;
* finite backward viability and lexicographically least viable paths;
* finite-list/height conversions for decidable predicates; and
* exact rational bisection for y^3 + y = x.

Only Python's standard library is used.  All arithmetic in the worked example
uses ``fractions.Fraction``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Hashable, Iterable, Mapping, Sequence, TypeVar


class CiferError(ValueError):
    """Raised when a finite interface violates its declared contract."""


@dataclass(frozen=True)
class Node:
    """One node of a fixed proof graph.

    ``kind`` is one of ``input``, ``local``, ``boundary``, or ``final``.
    Input nodes are permanent hypotheses and therefore never appear among
    residual obligations.  Boundary nodes have no local proof constructor.
    Local/final nodes may depend only on earlier nodes in a topological list.
    """

    name: str
    deps: tuple[str, ...] = ()
    kind: str = "local"
    statement: str = ""

    def __post_init__(self) -> None:
        if self.kind not in {"input", "local", "boundary", "final"}:
            raise CiferError(f"unknown node kind: {self.kind!r}")
        if self.kind == "boundary" and self.deps:
            raise CiferError("a primitive boundary node must not have dependencies")


@dataclass(frozen=True)
class ProofGraph:
    """A query-specialized finite proof graph in topological order."""

    nodes: tuple[Node, ...]

    def index(self) -> dict[str, int]:
        result: dict[str, int] = {}
        for i, node in enumerate(self.nodes):
            if node.name in result:
                raise CiferError(f"duplicate node name: {node.name}")
            result[node.name] = i
        return result

    def validate(self) -> None:
        idx = self.index()
        finals = 0
        for i, node in enumerate(self.nodes):
            if node.kind == "final":
                finals += 1
            for dep in node.deps:
                if dep not in idx:
                    raise CiferError(f"node {node.name} has unknown dependency {dep}")
                if idx[dep] >= i:
                    raise CiferError(
                        f"dependency {dep} of {node.name} is not earlier in topological order"
                    )
        if finals == 0:
            raise CiferError("proof graph has no final node")

    def node(self, name: str) -> Node:
        idx = self.index()
        try:
            return self.nodes[idx[name]]
        except KeyError as exc:
            raise CiferError(f"unknown node: {name}") from exc


def _stable_unique(xs: Iterable[str]) -> tuple[str, ...]:
    seen: set[str] = set()
    out: list[str] = []
    for x in xs:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return tuple(out)


def residual_boundaries(graph: ProofGraph, target: str) -> tuple[str, ...]:
    """Return the canonical dependency residual of ``target``.

    This expands local nodes backwards until reaching primitive boundary
    leaves.  Inputs are hypotheses and contribute no residual.  Duplicate
    leaves are removed in graph order.  The result is *dependency-normal*;
    it is not claimed to solve semantic minimization of logically equivalent
    assumptions.
    """

    graph.validate()
    idx = graph.index()
    if target not in idx:
        raise CiferError(f"unknown target: {target}")

    memo: dict[str, tuple[str, ...]] = {}

    def visit(name: str) -> tuple[str, ...]:
        if name in memo:
            return memo[name]
        node = graph.nodes[idx[name]]
        if node.kind == "boundary":
            ans = (name,)
        elif node.kind == "input":
            ans = ()
        else:
            ans = _stable_unique(x for dep in node.deps for x in visit(dep))
        memo[name] = ans
        return ans

    raw = visit(target)
    return tuple(sorted(raw, key=idx.__getitem__))


def reachable_subgraph(graph: ProofGraph, target: str) -> tuple[str, ...]:
    """Names of all nodes used by ``target``, in topological order."""

    graph.validate()
    idx = graph.index()
    if target not in idx:
        raise CiferError(f"unknown target: {target}")
    seen: set[str] = set()

    def visit(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        for dep in graph.nodes[idx[name]].deps:
            visit(dep)

    visit(target)
    return tuple(node.name for node in graph.nodes if node.name in seen)


def residual_report(graph: ProofGraph, target: str) -> dict[str, object]:
    """A machine-readable residual compilation summary."""

    residual = residual_boundaries(graph, target)
    reach = reachable_subgraph(graph, target)
    return {
        "target": target,
        "reachable_nodes": list(reach),
        "residual_boundaries": list(residual),
        "closed": not residual,
    }


Vector = tuple[int, ...]


def componentwise_le(a: Vector, b: Vector) -> bool:
    if len(a) != len(b):
        raise CiferError("dimension mismatch")
    return all(x <= y for x, y in zip(a, b, strict=True))


def componentwise_max(a: Vector, b: Vector) -> Vector:
    if len(a) != len(b):
        raise CiferError("dimension mismatch")
    return tuple(max(x, y) for x, y in zip(a, b, strict=True))


def demand_closure(
    seed: Sequence[int],
    cap: Sequence[int],
    transfer: Callable[[Vector], Sequence[int]],
) -> tuple[Vector, tuple[Vector, ...]]:
    """Compute the least capped inflationary closure above ``seed``.

    The caller supplies a monotone transfer function.  CIFER uses
    ``d_{s+1} = max(d_s, transfer(d_s))``.  Every strict step increases the
    coordinate sum, so a vector bounded by ``cap`` stabilizes after at most
    ``sum(cap) - sum(seed)`` strict increases.  The function checks the cap
    and returns the complete trace, which is suitable as finite evidence.
    """

    d = tuple(int(x) for x in seed)
    c = tuple(int(x) for x in cap)
    if len(d) != len(c):
        raise CiferError("seed/cap dimension mismatch")
    if any(x < 0 for x in d + c):
        raise CiferError("demands and caps must be natural numbers")
    if not componentwise_le(d, c):
        raise CiferError("seed exceeds cap")

    trace: list[Vector] = [d]
    max_steps = sum(c) - sum(d) + 1
    for _ in range(max_steps):
        proposed = tuple(int(x) for x in transfer(d))
        if len(proposed) != len(d) or any(x < 0 for x in proposed):
            raise CiferError("transfer returned an invalid demand vector")
        nxt = componentwise_max(d, proposed)
        if not componentwise_le(nxt, c):
            raise CiferError("demand closure exceeds the declared cap")
        if nxt == d:
            return d, tuple(trace)
        d = nxt
        trace.append(d)
    raise CiferError("inflationary closure did not stabilize within the rank bound")


T = TypeVar("T", bound=Hashable)


def backward_viability(
    levels: Sequence[Sequence[T]],
    compatible: Callable[[int, T, T], bool],
) -> tuple[tuple[frozenset[T], ...], tuple[T, ...] | None]:
    """Compute full-horizon viable sets and the lexicographically least path.

    ``compatible(k, x, y)`` means that candidate ``x`` at level ``k`` may be
    followed by ``y`` at level ``k+1``.  Candidates must be hashable and
    orderable for the canonical least-path extraction.
    """

    if not levels:
        return (), ()
    normalized = [tuple(level) for level in levels]
    if any(not level for level in normalized):
        return tuple(frozenset() for _ in normalized), None

    viable: list[set[T]] = [set() for _ in normalized]
    viable[-1] = set(normalized[-1])
    for k in range(len(normalized) - 2, -1, -1):
        viable[k] = {
            x
            for x in normalized[k]
            if any(compatible(k, x, y) for y in viable[k + 1])
        }

    if not viable[0]:
        return tuple(frozenset(v) for v in viable), None

    path: list[T] = [min(viable[0])]
    for k in range(len(normalized) - 1):
        successors = [
            y for y in viable[k + 1] if compatible(k, path[-1], y)
        ]
        if not successors:
            raise AssertionError("viability recurrence lost its successor")
        path.append(min(successors))
    return tuple(frozenset(v) for v in viable), tuple(path)


def stable_observation(
    witnesses: Sequence[T], observer: Callable[[T], Hashable]
) -> Hashable:
    """Return the common observation, or reject an unstable witness cloud."""

    if not witnesses:
        raise CiferError("stable observation requires a nonempty witness cloud")
    values = {observer(w) for w in witnesses}
    if len(values) != 1:
        raise CiferError(f"observer is not branch-independent: {sorted(map(str, values))}")
    return next(iter(values))


def diameter(values: Sequence[Fraction]) -> Fraction:
    if not values:
        raise CiferError("diameter requires a nonempty finite set")
    return max(values) - min(values)


def finite_height_bound(
    items: Sequence[T], height: Callable[[T], int]
) -> int:
    """A complete finite list yields an explicit maximum height bound."""

    if not items:
        return 0
    hs = [int(height(x)) for x in items]
    if any(h < 0 for h in hs):
        raise CiferError("height must be natural-valued")
    return max(hs)


def enumerate_bounded(
    bound: int, decode: Callable[[int], T], predicate: Callable[[T], bool]
) -> tuple[T, ...]:
    """Filter the complete code interval ``0..bound`` by a decidable predicate."""

    if bound < 0:
        raise CiferError("bound must be nonnegative")
    return tuple(x for code in range(bound + 1) if predicate(x := decode(code)))


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise CiferError("interval endpoints are reversed")

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    @property
    def midpoint(self) -> Fraction:
        return (self.lo + self.hi) / 2


def cubic_value(y: Fraction) -> Fraction:
    return y * y * y + y


def cubic_bisect(x: Fraction, steps: int) -> tuple[Interval, tuple[Interval, ...]]:
    """Bracket the unique root of ``y^3 + y = x`` by exact bisection.

    The initial interval ``[-M,M]`` with ``M=|x|+1`` has opposite signs for
    ``f(y)=y^3+y-x``.  Since ``f`` is strictly increasing, every bisection
    preserves the bracket and halves its width.
    """

    if steps < 0:
        raise CiferError("steps must be nonnegative")
    m = abs(x) + 1
    interval = Interval(-m, m)
    trace = [interval]
    for _ in range(steps):
        mid = interval.midpoint
        if cubic_value(mid) <= x:
            interval = Interval(mid, interval.hi)
        else:
            interval = Interval(interval.lo, mid)
        trace.append(interval)
    return interval, tuple(trace)


def check_cubic_trace(x: Fraction, trace: Sequence[Interval]) -> bool:
    if not trace:
        return False
    for i, interval in enumerate(trace):
        if not (cubic_value(interval.lo) <= x <= cubic_value(interval.hi)):
            return False
        if i and trace[i - 1].width != 2 * interval.width:
            return False
        if i and not (
            trace[i - 1].lo <= interval.lo <= interval.hi <= trace[i - 1].hi
        ):
            return False
    return True


def graph_from_mapping(spec: Sequence[Mapping[str, object]]) -> ProofGraph:
    """Build a graph from JSON-like dictionaries with strict validation."""

    nodes: list[Node] = []
    for raw in spec:
        try:
            name = str(raw["name"])
            kind = str(raw.get("kind", "local"))
            statement = str(raw.get("statement", ""))
            deps_raw = raw.get("deps", [])
        except Exception as exc:  # pragma: no cover - defensive input boundary
            raise CiferError(f"malformed node record: {raw!r}") from exc
        if not isinstance(deps_raw, (list, tuple)):
            raise CiferError(f"deps of {name} must be a list")
        nodes.append(Node(name, tuple(map(str, deps_raw)), kind, statement))
    graph = ProofGraph(tuple(nodes))
    graph.validate()
    return graph
