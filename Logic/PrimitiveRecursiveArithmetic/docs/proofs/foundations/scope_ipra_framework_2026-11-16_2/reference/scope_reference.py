#!/usr/bin/env python3
"""Executable reference model for SCOPE-iPRA.

This program is deliberately a semantic reference, not an object-iPRA proof.
It exercises the finite algorithms used by the report:
  * bounded-formula evaluation and Boolean reflection;
  * least bounded witnesses;
  * monotone capped demand closure;
  * certificate escape/effect checking;
  * exact and metric observer independence.
Only Python's standard library is used.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import argparse
import json
from typing import Any, Callable, Iterable, Mapping, Sequence

Env = tuple[int, ...]
Term = Callable[[Env], int]


class BForm:
    """Base class for fixed bounded formulas."""

    def eval(self, env: Env) -> bool:
        raise NotImplementedError

    def bit(self, env: Env) -> int:
        return 1 if self.eval(env) else 0


@dataclass(frozen=True)
class Eq(BForm):
    left: Term
    right: Term

    def eval(self, env: Env) -> bool:
        return self.left(env) == self.right(env)


@dataclass(frozen=True)
class Lt(BForm):
    left: Term
    right: Term

    def eval(self, env: Env) -> bool:
        return self.left(env) < self.right(env)


@dataclass(frozen=True)
class And(BForm):
    left: BForm
    right: BForm

    def eval(self, env: Env) -> bool:
        return self.left.eval(env) and self.right.eval(env)


@dataclass(frozen=True)
class Or(BForm):
    left: BForm
    right: BForm

    def eval(self, env: Env) -> bool:
        return self.left.eval(env) or self.right.eval(env)


@dataclass(frozen=True)
class Imp(BForm):
    left: BForm
    right: BForm

    def eval(self, env: Env) -> bool:
        return (not self.left.eval(env)) or self.right.eval(env)


@dataclass(frozen=True)
class Not(BForm):
    body: BForm

    def eval(self, env: Env) -> bool:
        return not self.body.eval(env)


@dataclass(frozen=True)
class ExistsLt(BForm):
    bound: Term
    body: BForm

    def eval(self, env: Env) -> bool:
        n = checked_nat(self.bound(env), "existential bound")
        return any(self.body.eval((i,) + env) for i in range(n))


@dataclass(frozen=True)
class ForallLt(BForm):
    bound: Term
    body: BForm

    def eval(self, env: Env) -> bool:
        n = checked_nat(self.bound(env), "universal bound")
        return all(self.body.eval((i,) + env) for i in range(n))


def var(index: int) -> Term:
    def term(env: Env) -> int:
        if not 0 <= index < len(env):
            raise IndexError(f"variable {index} outside environment of length {len(env)}")
        return env[index]

    return term


def const(value: int) -> Term:
    value = checked_nat(value, "constant")
    return lambda _env: value


def add(a: Term, b: Term) -> Term:
    return lambda env: a(env) + b(env)


def mul(a: Term, b: Term) -> Term:
    return lambda env: a(env) * b(env)


def checked_nat(value: int, label: str) -> int:
    if not isinstance(value, int) or value < 0:
        raise ValueError(f"{label} must be a natural number, got {value!r}")
    return value


def least_witness(bound: int, predicate: Callable[[int], bool]) -> int:
    """Return the least accepted code, or bound if no code is accepted."""
    bound = checked_nat(bound, "search bound")
    for witness in range(bound):
        if predicate(witness):
            return witness
    return bound


def witness_certificate(bound: int, predicate: Callable[[int], bool]) -> dict[str, Any]:
    witness = least_witness(bound, predicate)
    found = witness < bound
    return {
        "bound": bound,
        "witness": witness,
        "found": found,
        "accepted": bool(found and predicate(witness)),
        "minimal": bool(all(not predicate(i) for i in range(witness))),
    }


def capped_join(a: Sequence[int], b: Sequence[int], caps: Sequence[int]) -> tuple[int, ...]:
    if not (len(a) == len(b) == len(caps)):
        raise ValueError("vectors and caps must have the same length")
    return tuple(min(caps[i], max(a[i], b[i])) for i in range(len(caps)))


def demand_closure(
    transformer: Callable[[tuple[int, ...]], tuple[int, ...]],
    caps: Sequence[int],
    start: Sequence[int] | None = None,
) -> dict[str, Any]:
    """Least inflationary closure of a monotone capped finite transformer.

    The report proves stabilization in at most sum(caps) strict changes.  This
    reference implementation checks the same rank argument while executing.
    """

    caps_t = tuple(checked_nat(c, "capacity") for c in caps)
    state = tuple(0 for _ in caps_t) if start is None else tuple(start)
    if len(state) != len(caps_t):
        raise ValueError("start and caps must have the same length")
    if any(x < 0 or x > caps_t[i] for i, x in enumerate(state)):
        raise ValueError("start must lie within the capacity box")

    horizon = sum(caps_t) + 1
    trace: list[tuple[int, ...]] = [state]
    for _ in range(horizon):
        proposed = transformer(state)
        if len(proposed) != len(caps_t):
            raise ValueError("transformer returned a vector of the wrong dimension")
        proposed = tuple(checked_nat(x, "demand") for x in proposed)
        nxt = capped_join(state, proposed, caps_t)
        if nxt == state:
            return {
                "closure": list(state),
                "steps": len(trace) - 1,
                "trace": [list(x) for x in trace],
                "fixed": list(transformer(state)) == list(state),
                "prefixed": all(transformer(state)[i] <= state[i] for i in range(len(state))),
            }
        if sum(nxt) <= sum(state):
            raise AssertionError("a strict inflationary step failed to increase rank")
        state = nxt
        trace.append(state)
    raise AssertionError("closure did not stabilize within the rank bound")


ESCAPE_MODES = {"sealed", "relational", "named"}


@dataclass(frozen=True)
class ScopeNode:
    id: str
    deps: tuple[str, ...] = ()
    kind: str = "proof"
    escape: str = "sealed"
    has_producer: bool = True
    has_bound: bool = False
    observer_coherent: bool = False
    residual: str | None = None


@dataclass(frozen=True)
class ScopeIssue:
    node: str
    code: str
    message: str


def topological_order(nodes: Sequence[ScopeNode]) -> tuple[str, ...]:
    by_id = {node.id: node for node in nodes}
    if len(by_id) != len(nodes):
        raise ValueError("node identifiers must be unique")
    for node in nodes:
        missing = [dep for dep in node.deps if dep not in by_id]
        if missing:
            raise ValueError(f"node {node.id!r} has unknown dependencies {missing}")

    temporary: set[str] = set()
    permanent: set[str] = set()
    order: list[str] = []

    def visit(node_id: str) -> None:
        if node_id in permanent:
            return
        if node_id in temporary:
            raise ValueError(f"cycle detected at {node_id!r}; use a certified trace node")
        temporary.add(node_id)
        for dep in by_id[node_id].deps:
            visit(dep)
        temporary.remove(node_id)
        permanent.add(node_id)
        order.append(node_id)

    for node in nodes:
        visit(node.id)
    return tuple(order)


def check_scope_graph(nodes: Sequence[ScopeNode]) -> dict[str, Any]:
    order = topological_order(nodes)
    issues: list[ScopeIssue] = []
    residuals: list[str] = []

    for node in nodes:
        if node.escape not in ESCAPE_MODES:
            issues.append(ScopeIssue(node.id, "unknown_escape", f"unknown escape mode {node.escape!r}"))
            continue
        if not node.has_producer:
            if node.residual:
                residuals.append(node.residual)
            else:
                issues.append(
                    ScopeIssue(node.id, "missing_boundary", "missing producer must be exposed as a residual")
                )
        if node.escape == "named" and not (node.has_producer or node.has_bound):
            issues.append(
                ScopeIssue(
                    node.id,
                    "unjustified_name",
                    "a named witness needs a direct producer or a proved finite search bound",
                )
            )
        if node.escape == "relational" and not node.observer_coherent:
            issues.append(
                ScopeIssue(
                    node.id,
                    "unproved_observer",
                    "relational export needs an exact, quotient, or metric coherence proof",
                )
            )
        if node.escape == "sealed" and node.kind == "public_name":
            issues.append(
                ScopeIssue(node.id, "sealed_escape", "a sealed certificate cannot occur in a public name")
            )

    return {
        "ok": not issues,
        "topological_order": list(order),
        "residuals": sorted(set(residuals)),
        "issues": [asdict(issue) for issue in issues],
    }


def exact_observer_independent(
    valid_codes: Iterable[int], observer: Callable[[int], int]
) -> dict[str, Any]:
    codes = tuple(valid_codes)
    values = tuple(observer(code) for code in codes)
    independent = len(set(values)) <= 1
    return {"codes": list(codes), "values": list(values), "independent": independent}


def metric_observer_diameter(
    valid_codes: Iterable[int], observer: Callable[[int], int], tolerance: int
) -> dict[str, Any]:
    tolerance = checked_nat(tolerance, "tolerance")
    codes = tuple(valid_codes)
    values = tuple(observer(code) for code in codes)
    diameter = 0
    for a in values:
        for b in values:
            diameter = max(diameter, abs(a - b))
    return {
        "codes": list(codes),
        "values": list(values),
        "diameter": diameter,
        "tolerance": tolerance,
        "stable": diameter <= tolerance,
    }


def demo_payload() -> dict[str, Any]:
    # In a binder body, variable 0 is the new index and outer variables follow.
    nested = ForallLt(
        bound=const(5),
        body=ExistsLt(
            bound=const(7),
            body=Eq(var(0), add(var(1), const(1))),
        ),
    )

    search_demo = witness_certificate(20, lambda c: c * c >= 50)

    def cycle(d: tuple[int, ...]) -> tuple[int, ...]:
        a, b, c = d
        return min(4, b + 1), min(5, c + 1), min(3, a)

    closure_demo = demand_closure(cycle, (4, 5, 3))

    graph = [
        ScopeNode("input", kind="proof"),
        ScopeNode(
            "finite_cover",
            deps=("input",),
            kind="certificate",
            escape="sealed",
            has_producer=False,
            residual="ExistsFiniteCover",
        ),
        ScopeNode(
            "cluster_observer",
            deps=("finite_cover",),
            kind="observer",
            escape="relational",
            has_producer=True,
            observer_coherent=True,
        ),
        ScopeNode("goal", deps=("cluster_observer",), kind="proof"),
    ]

    invalid_graph = [
        ScopeNode(
            "branch_label",
            kind="public_name",
            escape="named",
            has_producer=False,
            has_bound=False,
        )
    ]

    return {
        "bounded_reflection": {
            "formula": "forall i<5, exists j<7, j=i+1",
            "truth": nested.eval(()),
            "bit": nested.bit(()),
        },
        "least_search": search_demo,
        "demand_closure": closure_demo,
        "scope_graph": check_scope_graph(graph),
        "rejected_escape": check_scope_graph(invalid_graph),
        "exact_observer": exact_observer_independent([2, 4, 8], lambda c: c % 2),
        "metric_observer": metric_observer_diameter([3, 4, 5], lambda c: 10 * c, 20),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON")
    args = parser.parse_args()
    print(json.dumps(demo_payload(), indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
