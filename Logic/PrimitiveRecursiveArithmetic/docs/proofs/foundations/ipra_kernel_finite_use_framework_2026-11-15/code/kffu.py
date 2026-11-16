"""Reference algorithms for the kernel-facing finite-use (KFFU) framework.

This module is deliberately small and exact.  It is *not* an iPRA proof
checker.  It exercises the finite algorithms whose correctness must be
represented by object-language derivations in the accompanying Lean plan.
Only Python's standard library is used.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Hashable, Iterable, Mapping, Sequence


class ContractError(ValueError):
    """Raised when a finite contract or certificate fails validation."""


@dataclass(frozen=True)
class ContractNode:
    """One node in a topologically ordered finite contract graph.

    ``run`` computes the node value from the already computed environment.
    ``verify`` is an independent finite checker for the result.  In an iPRA
    development, these are replaced by fixed primitive-recursive codes and an
    embedded proof that the checker is sound.
    """

    name: str
    parents: tuple[str, ...]
    run: Callable[[Mapping[str, Any]], Any]
    verify: Callable[[Mapping[str, Any], Any], bool]


@dataclass(frozen=True)
class TraceEntry:
    name: str
    parents: tuple[str, ...]
    parent_values: tuple[Any, ...]
    value: Any


def compile_contract_dag(
    nodes: Sequence[ContractNode],
    initial: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any], tuple[TraceEntry, ...]]:
    """Evaluate and validate a topologically ordered proof-carrying DAG.

    The function rejects duplicate names, forward references, failed local
    checkers, and attempts to overwrite initial data.  This mirrors the
    metatheoretic ``ProofBuild.step`` rule in ``lean/KernelCompiler.lean``.
    """

    env: dict[str, Any] = dict(initial or {})
    trace: list[TraceEntry] = []
    seen: set[str] = set(env)

    for node in nodes:
        if node.name in seen:
            raise ContractError(f"duplicate or overwritten node: {node.name}")
        missing = [parent for parent in node.parents if parent not in env]
        if missing:
            raise ContractError(
                f"node {node.name} has non-previous parents: {', '.join(missing)}"
            )
        value = node.run(env)
        if not node.verify(env, value):
            raise ContractError(f"local verifier failed at node {node.name}")
        env[node.name] = value
        seen.add(node.name)
        trace.append(
            TraceEntry(
                name=node.name,
                parents=node.parents,
                parent_values=tuple(env[parent] for parent in node.parents),
                value=value,
            )
        )

    return env, tuple(trace)


def backward_viability(
    layers: Sequence[Sequence[Hashable]],
    compatible: Callable[[int, Hashable, Hashable], bool],
) -> tuple[tuple[Hashable, ...], ...]:
    """Compute viable candidates in a finite layered relation.

    A candidate in layer ``i`` is viable when it has a compatible viable
    successor in layer ``i+1``.  The last layer is viable by definition.
    Duplicates are removed while preserving the input order.
    """

    if not layers:
        return ()
    if any(not layer for layer in layers):
        raise ContractError("every layer must be nonempty")

    def unique(xs: Iterable[Hashable]) -> tuple[Hashable, ...]:
        out: list[Hashable] = []
        used: set[Hashable] = set()
        for x in xs:
            if x not in used:
                used.add(x)
                out.append(x)
        return tuple(out)

    viable: list[tuple[Hashable, ...]] = [()] * len(layers)
    viable[-1] = unique(layers[-1])
    for i in range(len(layers) - 2, -1, -1):
        next_layer = viable[i + 1]
        viable[i] = unique(
            x
            for x in layers[i]
            if any(compatible(i, x, y) for y in next_layer)
        )
    return tuple(viable)


def lexicographic_viable_path(
    layers: Sequence[Sequence[Hashable]],
    compatible: Callable[[int, Hashable, Hashable], bool],
    key: Callable[[Hashable], Any] | None = None,
) -> tuple[Hashable, ...]:
    """Select the lexicographically first path using backward viability.

    No global choice principle is used: each selection is a bounded minimum
    in a finite coded list.  Failure is reported when no complete path exists.
    """

    viable = backward_viability(layers, compatible)
    if not viable:
        return ()
    order_key = key or (lambda x: x)
    if not viable[0]:
        raise ContractError("the layered relation has no complete path")

    path: list[Hashable] = [min(viable[0], key=order_key)]
    for i in range(len(viable) - 1):
        candidates = [
            y for y in viable[i + 1] if compatible(i, path[-1], y)
        ]
        if not candidates:  # Defensive: impossible if viability was computed correctly.
            raise ContractError("internal viability inconsistency")
        path.append(min(candidates, key=order_key))
    return tuple(path)


def enumerate_paths(
    layers: Sequence[Sequence[Hashable]],
    compatible: Callable[[int, Hashable, Hashable], bool],
) -> tuple[tuple[Hashable, ...], ...]:
    """Enumerate all complete paths; intended only for finite regression tests."""

    if not layers:
        return ((),)
    paths: list[tuple[Hashable, ...]] = [(x,) for x in layers[0]]
    for i in range(len(layers) - 1):
        paths = [
            path + (y,)
            for path in paths
            for y in layers[i + 1]
            if compatible(i, path[-1], y)
        ]
    return tuple(paths)


def observation_diameter(
    paths: Sequence[Sequence[Hashable]],
    observe: Callable[[Sequence[Hashable]], Fraction],
) -> Fraction:
    """Exact diameter of a finite family of rational observations."""

    if not paths:
        raise ContractError("cannot observe an empty path family")
    values = [observe(path) for path in paths]
    return max(values) - min(values)


def ceil_log2_positive(n: int) -> int:
    """Least k with n <= 2**k, for positive integers n."""

    if n <= 0:
        raise ValueError("n must be positive")
    return (n - 1).bit_length()


def ceil_fraction(q: Fraction) -> int:
    """Constructive integer ceiling for a rational number."""

    return -((-q.numerator) // q.denominator)


def cubic_value(y: Fraction, x: Fraction) -> Fraction:
    return y * y * y + y - x


def cubic_bisection_certificate(x: Fraction, precision: int) -> dict[str, Any]:
    """Produce an exact bracket for the unique root of y^3 + y = x.

    The result is finite data: a complete bisection trace with rational
    endpoints, sign checks, and a final width at most 2**(-precision).
    """

    if precision < 0:
        raise ValueError("precision must be nonnegative")

    radius = ceil_fraction(abs(x)) + 1
    steps = precision + ceil_log2_positive(2 * radius)
    lo = Fraction(-radius)
    hi = Fraction(radius)
    trace: list[dict[str, Any]] = []

    for stage in range(steps):
        mid = (lo + hi) / 2
        sign = cubic_value(mid, x)
        old_lo, old_hi = lo, hi
        if sign <= 0:
            lo = mid
            branch = "right"
        else:
            hi = mid
            branch = "left"
        trace.append(
            {
                "stage": stage,
                "lo": fraction_record(old_lo),
                "hi": fraction_record(old_hi),
                "mid": fraction_record(mid),
                "f_mid": fraction_record(sign),
                "branch": branch,
                "next_lo": fraction_record(lo),
                "next_hi": fraction_record(hi),
            }
        )

    certificate = {
        "equation": "y^3 + y = x",
        "x": fraction_record(x),
        "precision": precision,
        "radius": radius,
        "steps": steps,
        "initial_lo": fraction_record(Fraction(-radius)),
        "initial_hi": fraction_record(Fraction(radius)),
        "trace": trace,
        "final_lo": fraction_record(lo),
        "final_hi": fraction_record(hi),
        "final_width": fraction_record(hi - lo),
    }
    verify_cubic_bisection_certificate(certificate)
    return certificate


def verify_cubic_bisection_certificate(cert: Mapping[str, Any]) -> bool:
    """Independently verify every equation in a cubic bisection certificate."""

    x = fraction_from_record(cert["x"])
    precision = int(cert["precision"])
    radius = int(cert["radius"])
    steps = int(cert["steps"])
    if precision < 0 or radius != ceil_fraction(abs(x)) + 1:
        raise ContractError("incorrect precision or initial radius")
    if steps != precision + ceil_log2_positive(2 * radius):
        raise ContractError("incorrect bisection fuel")

    lo = fraction_from_record(cert["initial_lo"])
    hi = fraction_from_record(cert["initial_hi"])
    if lo != -radius or hi != radius:
        raise ContractError("incorrect initial endpoints")
    if cubic_value(lo, x) > 0 or cubic_value(hi, x) < 0:
        raise ContractError("initial sign bracket fails")

    trace = cert["trace"]
    if len(trace) != steps:
        raise ContractError("trace length does not equal fuel")

    for stage, row in enumerate(trace):
        if int(row["stage"]) != stage:
            raise ContractError("nonconsecutive trace stage")
        row_lo = fraction_from_record(row["lo"])
        row_hi = fraction_from_record(row["hi"])
        mid = fraction_from_record(row["mid"])
        sign = fraction_from_record(row["f_mid"])
        if row_lo != lo or row_hi != hi or mid != (lo + hi) / 2:
            raise ContractError(f"malformed midpoint at stage {stage}")
        if sign != cubic_value(mid, x):
            raise ContractError(f"incorrect polynomial value at stage {stage}")
        expected_branch = "right" if sign <= 0 else "left"
        if row["branch"] != expected_branch:
            raise ContractError(f"incorrect branch at stage {stage}")
        if expected_branch == "right":
            lo = mid
        else:
            hi = mid
        if fraction_from_record(row["next_lo"]) != lo:
            raise ContractError(f"incorrect next lower endpoint at stage {stage}")
        if fraction_from_record(row["next_hi"]) != hi:
            raise ContractError(f"incorrect next upper endpoint at stage {stage}")
        if cubic_value(lo, x) > 0 or cubic_value(hi, x) < 0:
            raise ContractError(f"sign invariant fails at stage {stage}")

    if fraction_from_record(cert["final_lo"]) != lo:
        raise ContractError("incorrect final lower endpoint")
    if fraction_from_record(cert["final_hi"]) != hi:
        raise ContractError("incorrect final upper endpoint")
    width = hi - lo
    if fraction_from_record(cert["final_width"]) != width:
        raise ContractError("incorrect final width")
    if width > Fraction(1, 2**precision):
        raise ContractError("requested precision was not reached")
    return True


def fraction_record(q: Fraction) -> dict[str, int]:
    return {"num": q.numerator, "den": q.denominator}


def fraction_from_record(value: Mapping[str, Any]) -> Fraction:
    den = int(value["den"])
    if den <= 0:
        raise ContractError("fraction denominator must be positive")
    q = Fraction(int(value["num"]), den)
    if q.numerator != int(value["num"]) or q.denominator != den:
        raise ContractError("fraction is not in normalized form")
    return q
