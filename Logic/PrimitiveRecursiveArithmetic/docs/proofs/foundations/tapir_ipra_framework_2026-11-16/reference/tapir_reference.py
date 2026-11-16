"""Exact host-level reference algorithms for TAPIR-iPRA.

This module is deliberately *not* an iPRA proof checker.  It validates and
normalizes finite contract graphs, computes residuals and certificate escape
modes, and provides executable counterparts of the finite algorithms discussed
in the report.  Logical soundness of a theorem must come from generated Lean
terms of type ``Prf PRAAx``.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum
from typing import Any, Callable, Iterable, Mapping, Sequence, TypeVar


T = TypeVar("T")


class GraphError(ValueError):
    """Raised when a finite proof graph is malformed."""


class EscapeMode(str, Enum):
    """How a certificate may cross a proof boundary."""

    LOCAL = "local"
    OBSERVED = "observed"
    NAMED = "named"


@dataclass(frozen=True)
class CertificateUse:
    """Syntactic information used by conservative escape analysis.

    ``appears_in_public`` means the certificate code itself, or data not known
    invariant under certificate change, appears in the public result.
    ``observer_proved`` means all public occurrences are under an observer with
    an exact or quantitative compatibility theorem.
    ``explicitly_named`` requests a public canonical/least code.
    """

    appears_in_public: bool = False
    observer_proved: bool = False
    explicitly_named: bool = False


@dataclass(frozen=True)
class Node:
    """One theorem-specialized local proof node."""

    ident: str
    conclusion: str
    deps: tuple[str, ...] = ()
    residuals: tuple[str, ...] = ()
    kind: str = "local"
    certificate: CertificateUse | None = None

    @staticmethod
    def from_mapping(obj: Mapping[str, Any]) -> "Node":
        cert_obj = obj.get("certificate")
        cert = None
        if cert_obj is not None:
            cert = CertificateUse(
                appears_in_public=bool(cert_obj.get("appears_in_public", False)),
                observer_proved=bool(cert_obj.get("observer_proved", False)),
                explicitly_named=bool(cert_obj.get("explicitly_named", False)),
            )
        return Node(
            ident=str(obj["id"]),
            conclusion=str(obj["conclusion"]),
            deps=tuple(str(x) for x in obj.get("deps", ())),
            residuals=tuple(str(x) for x in obj.get("residuals", ())),
            kind=str(obj.get("kind", "local")),
            certificate=cert,
        )


@dataclass(frozen=True)
class CompiledGraph:
    """Deterministic result of finite graph validation and slicing."""

    root: str
    reachable: tuple[str, ...]
    topological_order: tuple[str, ...]
    residuals: tuple[str, ...]
    escape_modes: tuple[tuple[str, EscapeMode], ...]

    def to_json_obj(self) -> dict[str, Any]:
        obj = asdict(self)
        obj["escape_modes"] = [
            {"node": node, "mode": mode.value} for node, mode in self.escape_modes
        ]
        return obj


def classify_escape(use: CertificateUse) -> EscapeMode:
    """Conservatively classify a certificate.

    Direct public naming wins.  A public occurrence is observed only when an
    observer compatibility theorem is explicitly recorded.  Everything else
    is proof-local.
    """

    if use.explicitly_named:
        return EscapeMode.NAMED
    if use.appears_in_public:
        return EscapeMode.OBSERVED if use.observer_proved else EscapeMode.NAMED
    return EscapeMode.LOCAL


def _index_nodes(nodes: Sequence[Node]) -> dict[str, Node]:
    index: dict[str, Node] = {}
    for node in nodes:
        if not node.ident:
            raise GraphError("node id must be nonempty")
        if node.ident in index:
            raise GraphError(f"duplicate node id: {node.ident}")
        if len(set(node.deps)) != len(node.deps):
            raise GraphError(f"duplicate dependency in node {node.ident}")
        index[node.ident] = node
    for node in nodes:
        for dep in node.deps:
            if dep not in index:
                raise GraphError(f"node {node.ident} depends on missing node {dep}")
    return index


def backward_slice(nodes: Sequence[Node], root: str) -> tuple[str, ...]:
    """Return reachable node ids in declaration order."""

    index = _index_nodes(nodes)
    if root not in index:
        raise GraphError(f"unknown root: {root}")
    reachable: set[str] = set()
    stack = [root]
    while stack:
        ident = stack.pop()
        if ident in reachable:
            continue
        reachable.add(ident)
        stack.extend(index[ident].deps)
    return tuple(node.ident for node in nodes if node.ident in reachable)


def topological_order(nodes: Sequence[Node], selected: Iterable[str] | None = None) -> tuple[str, ...]:
    """Stable Kahn topological order, preserving declaration order on ties."""

    index = _index_nodes(nodes)
    selected_set = set(index) if selected is None else set(selected)
    unknown = selected_set.difference(index)
    if unknown:
        raise GraphError(f"unknown selected nodes: {sorted(unknown)}")

    order_position = {node.ident: i for i, node in enumerate(nodes)}
    indegree = {ident: 0 for ident in selected_set}
    successors: dict[str, list[str]] = {ident: [] for ident in selected_set}
    for ident in selected_set:
        for dep in index[ident].deps:
            if dep not in selected_set:
                raise GraphError(
                    f"selected subgraph is not dependency closed: {ident} requires {dep}"
                )
            indegree[ident] += 1
            successors[dep].append(ident)

    ready = sorted((x for x, d in indegree.items() if d == 0), key=order_position.get)
    result: list[str] = []
    while ready:
        ident = ready.pop(0)
        result.append(ident)
        for succ in sorted(successors[ident], key=order_position.get):
            indegree[succ] -= 1
            if indegree[succ] == 0:
                ready.append(succ)
                ready.sort(key=order_position.get)

    if len(result) != len(selected_set):
        cyclic = sorted(x for x, d in indegree.items() if d > 0)
        raise GraphError(f"cycle detected among nodes: {cyclic}")
    return tuple(result)


def compile_graph(nodes: Sequence[Node], root: str) -> CompiledGraph:
    """Validate, slice, schedule, and collect exact syntactic residuals."""

    index = _index_nodes(nodes)
    reachable = backward_slice(nodes, root)
    order = topological_order(nodes, reachable)

    residuals: list[str] = []
    seen_residuals: set[str] = set()
    modes: list[tuple[str, EscapeMode]] = []
    for ident in order:
        node = index[ident]
        for residual in node.residuals:
            if residual not in seen_residuals:
                seen_residuals.add(residual)
                residuals.append(residual)
        if node.certificate is not None:
            modes.append((ident, classify_escape(node.certificate)))

    return CompiledGraph(
        root=root,
        reachable=reachable,
        topological_order=order,
        residuals=tuple(residuals),
        escape_modes=tuple(modes),
    )


def least_accepted(limit: int, predicate: Callable[[int], bool]) -> int | None:
    """Least accepted candidate below ``limit``; ``None`` when absent."""

    if limit < 0:
        raise ValueError("limit must be nonnegative")
    for candidate in range(limit):
        if predicate(candidate):
            return candidate
    return None


def synthesize_strategy(
    domain_size: int,
    response_bound: Callable[[int], int],
    relation: Callable[[int, int], bool],
) -> tuple[int, ...] | None:
    """Least pointwise strategy for ``forall x<N, exists y<M(x), R(x,y)``."""

    if domain_size < 0:
        raise ValueError("domain_size must be nonnegative")
    strategy: list[int] = []
    for x in range(domain_size):
        bound = response_bound(x)
        if bound < 0:
            raise ValueError(f"negative response bound at {x}")
        witness = least_accepted(bound, lambda y, x=x: relation(x, y))
        if witness is None:
            return None
        strategy.append(witness)
    return tuple(strategy)


def verify_strategy(
    strategy: Sequence[int],
    response_bound: Callable[[int], int],
    relation: Callable[[int, int], bool],
) -> bool:
    """Check a finite response table."""

    return all(0 <= y < response_bound(x) and relation(x, y) for x, y in enumerate(strategy))


def mixed_radix_encode(digits: Sequence[int], radices: Sequence[int]) -> int:
    """Encode bounded digits in little-endian mixed radix."""

    if len(digits) != len(radices):
        raise ValueError("digits and radices must have the same length")
    code = 0
    multiplier = 1
    for i, (digit, radix) in enumerate(zip(digits, radices, strict=True)):
        if radix <= 0:
            raise ValueError(f"radix {i} must be positive")
        if not 0 <= digit < radix:
            raise ValueError(f"digit {i}={digit} is outside [0,{radix})")
        code += digit * multiplier
        multiplier *= radix
    return code


def mixed_radix_decode(code: int, radices: Sequence[int]) -> tuple[int, ...]:
    """Decode a little-endian mixed-radix code."""

    if code < 0:
        raise ValueError("code must be nonnegative")
    digits: list[int] = []
    rest = code
    for i, radix in enumerate(radices):
        if radix <= 0:
            raise ValueError(f"radix {i} must be positive")
        digits.append(rest % radix)
        rest //= radix
    if rest:
        raise ValueError("code exceeds the declared mixed-radix space")
    return tuple(digits)


def monotone_demand_closure(
    initial: Sequence[int],
    capacities: Sequence[int],
    demand: Callable[[tuple[int, ...]], Sequence[int]],
) -> tuple[int, ...]:
    """Least prefixed point of ``d |-> d join demand(d)`` on finite chains.

    The function checks range and monotone progress along the generated chain.
    It does not universally verify that ``demand`` is monotone; that property is
    a theorem/proof obligation in a formal client.
    """

    if len(initial) != len(capacities):
        raise ValueError("initial and capacities must have the same length")
    if any(cap < 0 for cap in capacities):
        raise ValueError("capacities must be nonnegative")
    current = tuple(initial)
    if any(x < 0 or x > cap for x, cap in zip(current, capacities, strict=True)):
        raise ValueError("initial demand lies outside the finite chain")

    max_strict_steps = sum(cap - x for x, cap in zip(current, capacities, strict=True))
    for _ in range(max_strict_steps + 1):
        proposed = tuple(demand(current))
        if len(proposed) != len(current):
            raise ValueError("demand function changed dimension")
        if any(x < 0 or x > cap for x, cap in zip(proposed, capacities, strict=True)):
            raise ValueError("demand function left the finite chain")
        next_value = tuple(max(a, b) for a, b in zip(current, proposed, strict=True))
        if next_value == current:
            return current
        if not all(a <= b for a, b in zip(current, next_value, strict=True)):
            raise AssertionError("join update was not inflationary")
        current = next_value
    raise GraphError("finite demand closure failed to stabilize within capacity bound")


def run_trace(
    initial: T,
    step: Callable[[int, T], T],
    horizon: int,
    invariant: Callable[[int, T], bool] | None = None,
) -> tuple[T, ...]:
    """Run an exact finite trace and optionally check an invariant at every state."""

    if horizon < 0:
        raise ValueError("horizon must be nonnegative")
    states: list[T] = [initial]
    if invariant is not None and not invariant(0, initial):
        raise GraphError("invariant fails at the initial state")
    for t in range(horizon):
        nxt = step(t, states[-1])
        states.append(nxt)
        if invariant is not None and not invariant(t + 1, nxt):
            raise GraphError(f"invariant fails at time {t + 1}")
    return tuple(states)


def run_decreasing_until_done(
    initial: T,
    done: Callable[[T], bool],
    step: Callable[[T], T],
    measure: Callable[[T], int],
) -> tuple[T, ...]:
    """Execute a stopped run, validating strict measure decrease.

    At most ``measure(initial)+1`` transitions are attempted, matching the
    checked termination theorem's fuel bound.
    """

    m0 = measure(initial)
    if m0 < 0:
        raise ValueError("measure must be nonnegative")
    states: list[T] = [initial]
    for _ in range(m0 + 1):
        current = states[-1]
        if done(current):
            return tuple(states)
        nxt = step(current)
        if measure(nxt) >= measure(current):
            raise GraphError("nonterminal step did not strictly decrease the measure")
        states.append(nxt)
    if not done(states[-1]):
        raise GraphError("run did not terminate within the verified measure bound")
    return tuple(states)


def observer_diameter(values: Sequence[T], distance: Callable[[T, T], float]) -> float:
    """Maximum pairwise distance in a finite certificate cloud."""

    diameter = 0.0
    for i, left in enumerate(values):
        for right in values[i + 1 :]:
            d = distance(left, right)
            if d < 0:
                raise ValueError("distance must be nonnegative")
            diameter = max(diameter, d)
    return diameter


def spanning_tree_error(
    root: str,
    parent: Mapping[str, str | None],
    edge_error: Mapping[tuple[str, str], float],
) -> dict[str, float]:
    """Accumulate observer compatibility errors along a rooted tree."""

    if parent.get(root, object()) is not None:
        raise GraphError("root must have parent None")
    result: dict[str, float] = {root: 0.0}
    remaining = set(parent).difference({root})
    while remaining:
        progressed = False
        for node in list(remaining):
            p = parent[node]
            if p in result:
                key = (p, node)
                reverse = (node, p)
                if key in edge_error:
                    err = edge_error[key]
                elif reverse in edge_error:
                    err = edge_error[reverse]
                else:
                    raise GraphError(f"missing edge error for {p}-{node}")
                if err < 0:
                    raise ValueError("edge errors must be nonnegative")
                result[node] = result[p] + err
                remaining.remove(node)
                progressed = True
        if not progressed:
            raise GraphError("parent relation is cyclic or disconnected from the root")
    return result


__all__ = [
    "CertificateUse",
    "CompiledGraph",
    "EscapeMode",
    "GraphError",
    "Node",
    "backward_slice",
    "classify_escape",
    "compile_graph",
    "least_accepted",
    "mixed_radix_decode",
    "mixed_radix_encode",
    "monotone_demand_closure",
    "observer_diameter",
    "run_decreasing_until_done",
    "run_trace",
    "spanning_tree_error",
    "synthesize_strategy",
    "topological_order",
    "verify_strategy",
]
