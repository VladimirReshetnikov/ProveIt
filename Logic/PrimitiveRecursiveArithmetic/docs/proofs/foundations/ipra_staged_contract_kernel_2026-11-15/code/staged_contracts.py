"""Exact reference algorithms for the staged-contract iPRA framework.

This module is executable evidence only.  It models the finite host-side
passes that emit concrete primitive-recursive programs and object-theory proof
terms.  It is not an iPRA proof checker and never converts Python truth into an
object-theory theorem.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Callable, Dict, Hashable, Iterable, Mapping, Sequence


class ContractError(ValueError):
    """Raised when a finite contract is malformed or its obligations fail."""


def least_search(bound: int, predicate: Callable[[int], bool]) -> int | None:
    """Return the least i < bound satisfying predicate, or None.

    The loop is a direct executable model of bounded least search.  In iPRA
    the corresponding program is a fixed primitive recursion with a
    quantifier-free invariant recording whether a least witness has appeared.
    """
    if bound < 0:
        raise ContractError("bound must be nonnegative")
    for i in range(bound):
        if predicate(i):
            return i
    return None


def enumerate_bounded(bound: int, predicate: Callable[[int], bool]) -> list[int]:
    """List all i < bound satisfying a decidable predicate, without duplicates."""
    if bound < 0:
        raise ContractError("bound must be nonnegative")
    return [i for i in range(bound) if predicate(i)]


def lex_rank(counters: Sequence[int], caps: Sequence[int]) -> int:
    """Mixed-radix rank for a fixed finite tuple of resetting counters.

    Lexicographic descent (most significant coordinate first) strictly lowers
    this rank, even when less significant coordinates are reset to their caps.
    """
    if len(counters) != len(caps):
        raise ContractError("counter/cap arities differ")
    rank = 0
    for value, cap in zip(counters, caps):
        if cap < 0 or not 0 <= value <= cap:
            raise ContractError("counter outside its finite cap")
        rank = rank * (cap + 1) + value
    return rank


def check_strict_lex_descent(run: Sequence[Sequence[int]], caps: Sequence[int]) -> bool:
    """Check that every successive state has strictly smaller mixed-radix rank."""
    ranks = [lex_rank(state, caps) for state in run]
    return all(next_rank < rank for rank, next_rank in zip(ranks, ranks[1:]))


Demand = tuple[int, ...]
DemandTransformer = Callable[[Demand], Demand]


def componentwise_max(a: Demand, b: Demand) -> Demand:
    if len(a) != len(b):
        raise ContractError("demand arities differ")
    return tuple(max(x, y) for x, y in zip(a, b))


def bounded_demand_closure(
    initial: Demand,
    transformer: DemandTransformer,
    caps: Demand,
) -> tuple[Demand, list[Demand]]:
    """Compute a least inflationary fixed point inside a finite demand box.

    The caller supplies an inflationary monotone transformer.  This routine
    checks inflationarity and the cap dynamically.  A non-fixed iteration must
    increase the sum by at least one; therefore at most sum(caps-initial)
    iterations are possible.
    """
    if len(initial) != len(caps):
        raise ContractError("demand/cap arities differ")
    if any(c < 0 or x < 0 or x > c for x, c in zip(initial, caps)):
        raise ContractError("initial demand outside finite cap")

    current = initial
    trace = [current]
    fuel = sum(c - x for x, c in zip(initial, caps)) + 1
    for _ in range(fuel):
        proposed = transformer(current)
        if len(proposed) != len(current):
            raise ContractError("transformer changed demand arity")
        if any(y < x for x, y in zip(current, proposed)):
            raise ContractError("transformer is not inflationary on the trace")
        if any(y > c for y, c in zip(proposed, caps)):
            raise ContractError("transformer escaped the certified cap")
        trace.append(proposed)
        if proposed == current:
            return current, trace
        current = proposed
    raise ContractError("finite-lattice fuel exhausted before a fixed point")


@dataclass(frozen=True)
class ProofTerm:
    """A transparent host-side description of how an object proof is assembled."""

    rule: str
    conclusion: str
    premises: tuple["ProofTerm", ...] = ()
    metadata: Mapping[str, Any] = field(default_factory=dict)

    def node_count(self) -> int:
        return 1 + sum(p.node_count() for p in self.premises)


@dataclass(frozen=True)
class StaticNode:
    """One already-specialized node of a finite proof graph.

    ``local_proof`` stands for a concrete ``Prf PRAAx`` term.  Dependencies
    name prior conclusions that appear in its instantiated local context.
    """

    name: str
    dependencies: tuple[str, ...]
    conclusion: str
    local_rule: str = "local-Prf"
    payload: Mapping[str, Any] = field(default_factory=dict)


def compile_static_schedule(
    nodes: Sequence[StaticNode],
    base_hypotheses: Iterable[str] = (),
) -> dict[str, ProofTerm]:
    """Compile a topologically ordered graph by simultaneous cuts.

    A node can use a base hypothesis or an earlier node only.  The result is a
    proof-term tree recording specialization plus simultaneous cut.  In Lean,
    the corresponding trusted operations are ``Prf.subst``, ``Prf.weaken``,
    and ``Prf.trans``.
    """
    available_base = set(base_hypotheses)
    built: dict[str, ProofTerm] = {}
    for node in nodes:
        if node.name in built or node.name in available_base:
            raise ContractError(f"duplicate theorem name: {node.name}")
        missing = [d for d in node.dependencies if d not in built and d not in available_base]
        if missing:
            raise ContractError(
                f"node {node.name!r} is not topologically available; missing {missing}"
            )
        premises = tuple(
            built[d]
            if d in built
            else ProofTerm("hyp", d, (), {"base": True})
            for d in node.dependencies
        )
        local = ProofTerm(
            node.local_rule,
            node.conclusion,
            (),
            {"node": node.name, **dict(node.payload)},
        )
        built[node.name] = ProofTerm(
            "subst-weaken-trans",
            node.conclusion,
            premises + (local,),
            {"node": node.name, "dependencies": node.dependencies},
        )
    return built


Candidate = Hashable


def viable_sets(
    levels: Sequence[Sequence[Candidate]],
    edges: Sequence[Callable[[Candidate, Candidate], bool]],
) -> list[set[Candidate]]:
    """Backward finite viability for a layered relational witness cloud."""
    if not levels:
        raise ContractError("at least one level is required")
    if len(edges) != len(levels) - 1:
        raise ContractError("there must be one edge relation between adjacent levels")
    viable: list[set[Candidate]] = [set() for _ in levels]
    viable[-1] = set(levels[-1])
    for i in range(len(levels) - 2, -1, -1):
        viable[i] = {
            a
            for a in levels[i]
            if any(edges[i](a, b) for b in viable[i + 1])
        }
    return viable


def least_viable_path(
    levels: Sequence[Sequence[int]],
    edges: Sequence[Callable[[int, int], bool]],
) -> list[int] | None:
    """Choose the lexicographically least successful finite path."""
    viable = viable_sets(levels, edges)
    if not viable[0]:
        return None
    current = min(viable[0])
    path = [current]
    for i, edge in enumerate(edges):
        successors = [b for b in viable[i + 1] if edge(current, b)]
        if not successors:
            raise AssertionError("backward viability invariant was violated")
        current = min(successors)
        path.append(current)
    return path


def exact_stable_observable(
    candidates: Sequence[Candidate],
    observable: Callable[[Candidate], Hashable],
) -> Hashable:
    """Erase a finite internal choice when all certified branches agree exactly."""
    if not candidates:
        raise ContractError("a nonempty certified cloud is required")
    values = [observable(c) for c in candidates]
    first = values[0]
    if any(v != first for v in values[1:]):
        raise ContractError("observable is not branch independent")
    return first


def diameter_stable_observable(
    candidates: Sequence[Candidate],
    observable: Callable[[Candidate], Fraction],
    diameter: Fraction,
) -> Fraction:
    """Select a canonical branch after checking a rational diameter certificate."""
    if not candidates:
        raise ContractError("a nonempty certified cloud is required")
    if diameter < 0:
        raise ContractError("diameter must be nonnegative")
    values = [observable(c) for c in candidates]
    if max(values) - min(values) > diameter:
        raise ContractError("claimed diameter bound fails")
    # A fixed least-code selector models bounded least search.
    selected = min(candidates)
    return observable(selected)


def height_to_complete_list(
    height: int,
    predicate: Callable[[int], bool],
) -> list[int]:
    """Turn a proved height cutoff into a complete bounded enumeration."""
    if height < 0:
        raise ContractError("height must be nonnegative")
    return enumerate_bounded(height + 1, predicate)


def complete_list_to_height(values: Sequence[int]) -> int:
    """The maximum of an explicitly complete finite list is a cutoff."""
    if any(v < 0 for v in values):
        raise ContractError("codes must be natural numbers")
    return max(values, default=0)


@dataclass(frozen=True)
class CubicBracket:
    """An exact rational bracket for the root of y^3+y=x."""

    x: Fraction
    lo: Fraction
    hi: Fraction

    @staticmethod
    def f(y: Fraction) -> Fraction:
        return y * y * y + y

    def valid(self) -> bool:
        return self.lo <= self.hi and self.f(self.lo) <= self.x <= self.f(self.hi)

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    def bisect(self) -> "CubicBracket":
        if not self.valid():
            raise ContractError("invalid cubic bracket")
        mid = (self.lo + self.hi) / 2
        if self.f(mid) <= self.x:
            result = CubicBracket(self.x, mid, self.hi)
        else:
            result = CubicBracket(self.x, self.lo, mid)
        if not result.valid() or result.width * 2 != self.width:
            raise AssertionError("exact bisection invariant failed")
        return result


def initial_cubic_bracket(x: Fraction) -> CubicBracket:
    """A uniform primitive-recursive-style bracket using B=|x|+1."""
    bound = abs(x) + 1
    bracket = CubicBracket(x, -bound, bound)
    if not bracket.valid():
        raise AssertionError("uniform initial bracket theorem failed")
    return bracket


def cubic_bisection(x: Fraction, steps: int) -> tuple[CubicBracket, list[CubicBracket]]:
    """Run exact bisection with a replayable trace."""
    if steps < 0:
        raise ContractError("steps must be nonnegative")
    current = initial_cubic_bracket(x)
    trace = [current]
    for _ in range(steps):
        current = current.bisect()
        trace.append(current)
    return current, trace


def fraction_json(q: Fraction) -> dict[str, int]:
    return {"num": q.numerator, "den": q.denominator}
