"""Exact finite reference algorithms for the KIFC-S report.

The module validates the finite metadata algorithms used by the framework:
query reachability, residual-frontier normalization, topological schedules,
capped demand closure, bounded two-sided strategy certificates, finite
viability, stable observations, and rational bisection.

It is not an iPRA proof checker.  Logical soundness must ultimately be given by
Lean declarations whose endpoints are ``Prf PRAAx`` or checked translations.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any, Callable, Hashable, Iterable, Mapping, Sequence, TypeVar

T = TypeVar("T", bound=Hashable)


def _nonnegative(value: int, name: str) -> None:
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")


def stable_unique(values: Iterable[T]) -> tuple[T, ...]:
    """Remove duplicates while retaining the first occurrence."""
    seen: set[T] = set()
    answer: list[T] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            answer.append(value)
    return tuple(answer)


@dataclass(frozen=True)
class Boundary:
    key: str
    formula: str
    origin: str = ""
    expected_producer: str = ""


@dataclass(frozen=True)
class ProofNode:
    name: str
    parents: tuple[str, ...] = ()
    boundaries: tuple[Boundary, ...] = ()


@dataclass(frozen=True)
class QueryPlan:
    sinks: tuple[str, ...]
    reachable: tuple[str, ...]
    topological: tuple[str, ...]
    residuals: tuple[Boundary, ...]


def backward_reachable(
    nodes: Mapping[str, ProofNode], sinks: Sequence[str]
) -> frozenset[str]:
    """Least parent-closed set containing ``sinks``."""
    unknown = [name for name in sinks if name not in nodes]
    if unknown:
        raise KeyError(f"unknown sink(s): {unknown}")
    marked: set[str] = set()
    work = list(reversed(tuple(sinks)))
    while work:
        name = work.pop()
        if name in marked:
            continue
        marked.add(name)
        node = nodes[name]
        for parent in reversed(node.parents):
            if parent not in nodes:
                raise KeyError(f"node {name!r} has unknown parent {parent!r}")
            if parent not in marked:
                work.append(parent)
    return frozenset(marked)


def topological_order(
    nodes: Mapping[str, ProofNode], subset: Iterable[str]
) -> tuple[str, ...]:
    """Stable Kahn order of a parent-before-child proof subgraph."""
    chosen = frozenset(subset)
    indegree = {
        name: sum(parent in chosen for parent in nodes[name].parents)
        for name in chosen
    }
    children: dict[str, list[str]] = {name: [] for name in chosen}
    for name in chosen:
        for parent in nodes[name].parents:
            if parent in chosen:
                children[parent].append(name)
    ready = sorted(name for name, degree in indegree.items() if degree == 0)
    answer: list[str] = []
    while ready:
        name = ready.pop(0)
        answer.append(name)
        for child in sorted(children[name]):
            indegree[child] -= 1
            if indegree[child] == 0:
                ready.append(child)
                ready.sort()
    if len(answer) != len(chosen):
        cyclic = sorted(name for name, degree in indegree.items() if degree > 0)
        raise ValueError(f"logical proof cycle: {cyclic}")
    return tuple(answer)


def compile_query_plan(
    nodes: Mapping[str, ProofNode], sinks: Sequence[str]
) -> QueryPlan:
    """Compute the query slice and its stable residual frontier."""
    reachable_set = backward_reachable(nodes, sinks)
    topo = topological_order(nodes, reachable_set)
    boundary_by_key: dict[str, Boundary] = {}
    for name in topo:
        for boundary in nodes[name].boundaries:
            previous = boundary_by_key.get(boundary.key)
            if previous is not None and previous.formula != boundary.formula:
                raise ValueError(
                    f"boundary key {boundary.key!r} has incompatible formulas"
                )
            boundary_by_key.setdefault(boundary.key, boundary)
    residuals = tuple(boundary_by_key[key] for key in sorted(boundary_by_key))
    return QueryPlan(
        sinks=tuple(sinks),
        reachable=tuple(sorted(reachable_set)),
        topological=topo,
        residuals=residuals,
    )


def is_parent_closed(
    nodes: Mapping[str, ProofNode], subset: Iterable[str]
) -> bool:
    chosen = frozenset(subset)
    return all(
        parent in chosen
        for name in chosen
        for parent in nodes[name].parents
    )


def reachability_is_least(
    nodes: Mapping[str, ProofNode], sinks: Sequence[str], candidate: Iterable[str]
) -> bool:
    candidate_set = frozenset(candidate)
    if not set(sinks) <= candidate_set or not is_parent_closed(nodes, candidate_set):
        return False
    return backward_reachable(nodes, sinks) <= candidate_set


@dataclass(frozen=True)
class DemandEdge:
    provider: str
    consumer: str
    transform: Callable[[int], int]


@dataclass(frozen=True)
class DemandClosure:
    vector: Mapping[str, int]
    states: tuple[Mapping[str, int], ...]
    fixed: bool
    overflow: bool
    overflow_edges: tuple[tuple[str, str, int, int], ...]


@dataclass(frozen=True)
class CappedDemandSystem:
    nodes: tuple[str, ...]
    seed: Mapping[str, int]
    cap: Mapping[str, int]
    edges: tuple[DemandEdge, ...]

    def __post_init__(self) -> None:
        if len(set(self.nodes)) != len(self.nodes):
            raise ValueError("demand node names must be unique")
        names = set(self.nodes)
        if set(self.seed) != names or set(self.cap) != names:
            raise ValueError("seed and cap must name every demand node exactly")
        for name in self.nodes:
            _nonnegative(self.seed[name], f"seed[{name}]")
            _nonnegative(self.cap[name], f"cap[{name}]")
            if self.seed[name] > self.cap[name]:
                raise ValueError("seed exceeds cap")
        for edge in self.edges:
            if edge.provider not in names or edge.consumer not in names:
                raise ValueError("unknown demand edge endpoint")

    def raw_update(self, vector: Mapping[str, int]) -> dict[str, int]:
        result = {name: max(self.seed[name], vector[name]) for name in self.nodes}
        for edge in self.edges:
            request = edge.transform(vector[edge.consumer])
            _nonnegative(request, "transformed demand")
            result[edge.provider] = max(result[edge.provider], request)
        return result

    def step(self, vector: Mapping[str, int]) -> tuple[dict[str, int], tuple[tuple[str, str, int, int], ...]]:
        raw = self.raw_update(vector)
        overflow: list[tuple[str, str, int, int]] = []
        for edge in self.edges:
            request = edge.transform(vector[edge.consumer])
            if request > self.cap[edge.provider]:
                overflow.append((edge.provider, edge.consumer, request, self.cap[edge.provider]))
        capped = {name: min(raw[name], self.cap[name]) for name in self.nodes}
        return capped, tuple(overflow)

    def rank(self, vector: Mapping[str, int]) -> int:
        """Consumed-cap rank, increasing on every strict inflationary step."""
        return sum(vector[name] - self.seed[name] for name in self.nodes)

    def close(self) -> DemandClosure:
        vector = dict(self.seed)
        states: list[Mapping[str, int]] = [dict(vector)]
        overflows: list[tuple[str, str, int, int]] = []
        maximum_rounds = 1 + sum(self.cap[name] - self.seed[name] for name in self.nodes)
        for _ in range(maximum_rounds):
            nxt, step_overflow = self.step(vector)
            overflows.extend(step_overflow)
            if nxt == vector:
                return DemandClosure(
                    vector=dict(vector),
                    states=tuple(states),
                    fixed=True,
                    overflow=bool(overflows),
                    overflow_edges=stable_unique(overflows),
                )
            vector = nxt
            states.append(dict(vector))
        raise AssertionError("finite inflationary demand iteration did not stabilize")

    def closed(self, vector: Mapping[str, int]) -> bool:
        return all(
            vector[name] >= self.seed[name] and vector[name] <= self.cap[name]
            for name in self.nodes
        ) and all(
            vector[edge.provider] >= edge.transform(vector[edge.consumer])
            for edge in self.edges
        )

    def least_against(self, candidate: Mapping[str, int]) -> bool:
        result = self.close().vector
        if not self.closed(candidate):
            return False
        return all(result[name] <= candidate[name] for name in self.nodes)


# Fixed bounded formula syntax and two-sided certificates.
@dataclass(frozen=True)
class Atom:
    name: str
    predicate: Callable[[Mapping[str, int]], bool]


@dataclass(frozen=True)
class And:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Forall:
    variable: str
    bound: Callable[[Mapping[str, int]], int]
    body: "Formula"


@dataclass(frozen=True)
class Exists:
    variable: str
    bound: Callable[[Mapping[str, int]], int]
    body: "Formula"


Formula = Atom | And | Or | Forall | Exists


@dataclass(frozen=True)
class TruthCert:
    tag: str
    payload: Any = None


@dataclass(frozen=True)
class FalseCert:
    tag: str
    payload: Any = None


def eval_formula(formula: Formula, env: Mapping[str, int]) -> bool:
    if isinstance(formula, Atom):
        return bool(formula.predicate(env))
    if isinstance(formula, And):
        return eval_formula(formula.left, env) and eval_formula(formula.right, env)
    if isinstance(formula, Or):
        return eval_formula(formula.left, env) or eval_formula(formula.right, env)
    if isinstance(formula, Forall):
        bound = formula.bound(env)
        _nonnegative(bound, "universal bound")
        return all(
            eval_formula(formula.body, {**env, formula.variable: value})
            for value in range(bound)
        )
    if isinstance(formula, Exists):
        bound = formula.bound(env)
        _nonnegative(bound, "existential bound")
        return any(
            eval_formula(formula.body, {**env, formula.variable: value})
            for value in range(bound)
        )
    raise TypeError(formula)


def truth_certificate(formula: Formula, env: Mapping[str, int]) -> TruthCert:
    if not eval_formula(formula, env):
        raise ValueError("formula is false")
    if isinstance(formula, Atom):
        return TruthCert("atom")
    if isinstance(formula, And):
        return TruthCert(
            "and",
            (truth_certificate(formula.left, env), truth_certificate(formula.right, env)),
        )
    if isinstance(formula, Or):
        if eval_formula(formula.left, env):
            return TruthCert("or-left", truth_certificate(formula.left, env))
        return TruthCert("or-right", truth_certificate(formula.right, env))
    if isinstance(formula, Forall):
        bound = formula.bound(env)
        return TruthCert(
            "forall",
            tuple(
                truth_certificate(formula.body, {**env, formula.variable: value})
                for value in range(bound)
            ),
        )
    if isinstance(formula, Exists):
        bound = formula.bound(env)
        witness = next(
            value
            for value in range(bound)
            if eval_formula(formula.body, {**env, formula.variable: value})
        )
        subenv = {**env, formula.variable: witness}
        return TruthCert("exists", (witness, truth_certificate(formula.body, subenv)))
    raise TypeError(formula)


def false_certificate(formula: Formula, env: Mapping[str, int]) -> FalseCert:
    if eval_formula(formula, env):
        raise ValueError("formula is true")
    if isinstance(formula, Atom):
        return FalseCert("atom")
    if isinstance(formula, And):
        if not eval_formula(formula.left, env):
            return FalseCert("and-left", false_certificate(formula.left, env))
        return FalseCert("and-right", false_certificate(formula.right, env))
    if isinstance(formula, Or):
        return FalseCert(
            "or",
            (false_certificate(formula.left, env), false_certificate(formula.right, env)),
        )
    if isinstance(formula, Forall):
        bound = formula.bound(env)
        witness = next(
            value
            for value in range(bound)
            if not eval_formula(formula.body, {**env, formula.variable: value})
        )
        subenv = {**env, formula.variable: witness}
        return FalseCert("forall", (witness, false_certificate(formula.body, subenv)))
    if isinstance(formula, Exists):
        bound = formula.bound(env)
        return FalseCert(
            "exists",
            tuple(
                false_certificate(formula.body, {**env, formula.variable: value})
                for value in range(bound)
            ),
        )
    raise TypeError(formula)


def check_truth(formula: Formula, env: Mapping[str, int], cert: TruthCert) -> bool:
    if isinstance(formula, Atom):
        return cert.tag == "atom" and eval_formula(formula, env)
    if isinstance(formula, And):
        return (
            cert.tag == "and"
            and isinstance(cert.payload, tuple)
            and len(cert.payload) == 2
            and check_truth(formula.left, env, cert.payload[0])
            and check_truth(formula.right, env, cert.payload[1])
        )
    if isinstance(formula, Or):
        if cert.tag == "or-left":
            return check_truth(formula.left, env, cert.payload)
        if cert.tag == "or-right":
            return check_truth(formula.right, env, cert.payload)
        return False
    if isinstance(formula, Forall):
        bound = formula.bound(env)
        return (
            cert.tag == "forall"
            and isinstance(cert.payload, tuple)
            and len(cert.payload) == bound
            and all(
                check_truth(
                    formula.body,
                    {**env, formula.variable: value},
                    cert.payload[value],
                )
                for value in range(bound)
            )
        )
    if isinstance(formula, Exists):
        if cert.tag != "exists" or not isinstance(cert.payload, tuple) or len(cert.payload) != 2:
            return False
        witness, subcert = cert.payload
        bound = formula.bound(env)
        return (
            isinstance(witness, int)
            and 0 <= witness < bound
            and check_truth(
                formula.body, {**env, formula.variable: witness}, subcert
            )
        )
    raise TypeError(formula)


def check_false(formula: Formula, env: Mapping[str, int], cert: FalseCert) -> bool:
    if isinstance(formula, Atom):
        return cert.tag == "atom" and not eval_formula(formula, env)
    if isinstance(formula, And):
        if cert.tag == "and-left":
            return check_false(formula.left, env, cert.payload)
        if cert.tag == "and-right":
            return check_false(formula.right, env, cert.payload)
        return False
    if isinstance(formula, Or):
        return (
            cert.tag == "or"
            and isinstance(cert.payload, tuple)
            and len(cert.payload) == 2
            and check_false(formula.left, env, cert.payload[0])
            and check_false(formula.right, env, cert.payload[1])
        )
    if isinstance(formula, Forall):
        if cert.tag != "forall" or not isinstance(cert.payload, tuple) or len(cert.payload) != 2:
            return False
        witness, subcert = cert.payload
        bound = formula.bound(env)
        return (
            isinstance(witness, int)
            and 0 <= witness < bound
            and check_false(
                formula.body, {**env, formula.variable: witness}, subcert
            )
        )
    if isinstance(formula, Exists):
        bound = formula.bound(env)
        return (
            cert.tag == "exists"
            and isinstance(cert.payload, tuple)
            and len(cert.payload) == bound
            and all(
                check_false(
                    formula.body,
                    {**env, formula.variable: value},
                    cert.payload[value],
                )
                for value in range(bound)
            )
        )
    raise TypeError(formula)


@dataclass(frozen=True)
class RelationTower:
    levels: tuple[tuple[T, ...], ...]
    edge: Callable[[int, T, T], bool]
    valid: Callable[[int, T], bool] = lambda _level, _value: True
    terminal: Callable[[T], bool] = lambda _value: True

    def __post_init__(self) -> None:
        if not self.levels:
            raise ValueError("relation tower must have at least one level")
        for level in self.levels:
            if len(set(level)) != len(level):
                raise ValueError("a relation level contains duplicate codes")

    def viable(self, horizon: int) -> tuple[frozenset[T], ...]:
        if not 0 <= horizon < len(self.levels):
            raise ValueError("invalid horizon")
        rows: list[set[T]] = [set() for _ in range(horizon + 1)]
        rows[horizon] = {
            value
            for value in self.levels[horizon]
            if self.valid(horizon, value) and self.terminal(value)
        }
        for level in range(horizon - 1, -1, -1):
            rows[level] = {
                value
                for value in self.levels[level]
                if self.valid(level, value)
                and any(self.edge(level, value, nxt) for nxt in rows[level + 1])
            }
        return tuple(frozenset(row) for row in rows)

    def brute_paths(self, start: int, horizon: int, first: T | None = None) -> tuple[tuple[T, ...], ...]:
        rows = self.levels[start : horizon + 1]
        answer: list[tuple[T, ...]] = []
        for path in product(*rows):
            if first is not None and path[0] != first:
                continue
            if any(not self.valid(start + offset, value) for offset, value in enumerate(path)):
                continue
            if not self.terminal(path[-1]):
                continue
            if all(
                self.edge(start + offset, path[offset], path[offset + 1])
                for offset in range(len(path) - 1)
            ):
                answer.append(tuple(path))
        return tuple(answer)

    def viability_matches_paths(self, horizon: int) -> bool:
        rows = self.viable(horizon)
        return all(
            (value in rows[level]) == bool(self.brute_paths(level, horizon, value))
            for level in range(horizon + 1)
            for value in self.levels[level]
        )

    def least_path(self, horizon: int, key: Callable[[T], Any] | None = None) -> tuple[T, ...]:
        rows = self.viable(horizon)
        order = key or (lambda value: value)
        if not rows[0]:
            raise ValueError("no viable start")
        current = min(rows[0], key=order)
        path = [current]
        for level in range(horizon):
            successors = [
                nxt
                for nxt in rows[level + 1]
                if self.edge(level, current, nxt)
            ]
            if not successors:
                raise AssertionError("viability row has no viable successor")
            current = min(successors, key=order)
            path.append(current)
        return tuple(path)


def stable_observation(
    candidates: Sequence[T], observer: Callable[[T], Any]
) -> Any:
    if not candidates:
        raise ValueError("empty candidate cloud")
    values = [observer(candidate) for candidate in candidates]
    if any(value != values[0] for value in values[1:]):
        raise ValueError("observer is not exact-stable")
    return values[0]


def observation_diameter(
    candidates: Sequence[T],
    observer: Callable[[T], Fraction],
) -> Fraction:
    if not candidates:
        raise ValueError("empty candidate cloud")
    values = [observer(candidate) for candidate in candidates]
    return max(abs(left - right) for left in values for right in values)


def tail_sum(terms: Sequence[Fraction], start: int, stop: int) -> Fraction:
    if not 0 <= start <= stop <= len(terms):
        raise ValueError("invalid tail range")
    return sum(terms[start:stop], Fraction(0))


@dataclass(frozen=True)
class BisectionState:
    lower: Fraction
    upper: Fraction


def cubic(value: Fraction) -> Fraction:
    return value**3 + value


def cubic_bisection(x: Fraction, steps: int) -> tuple[BisectionState, ...]:
    _nonnegative(steps, "steps")
    radius = abs(x) + 1
    state = BisectionState(-radius, radius)
    states = [state]
    if not cubic(state.lower) <= x <= cubic(state.upper):
        raise AssertionError("initial interval does not bracket")
    for _ in range(steps):
        middle = (state.lower + state.upper) / 2
        if cubic(middle) <= x:
            state = BisectionState(middle, state.upper)
        else:
            state = BisectionState(state.lower, middle)
        if not cubic(state.lower) <= x <= cubic(state.upper):
            raise AssertionError("bisection lost bracket")
        states.append(state)
    return tuple(states)
