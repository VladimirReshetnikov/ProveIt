"""Reference algorithms for the OCiPRA finite-observation framework.

This module is deliberately small and exact.  It is *not* an iPRA proof
checker.  Its purpose is to make the finite algorithms in the accompanying
paper executable: bounded search, demand closure, contract-DAG evaluation,
finite relational viability, and theorem-profile diagnostics.

All arithmetic in the examples is integer or ``fractions.Fraction`` arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from itertools import product
from typing import Any, Callable, Iterable, Mapping, Sequence


class ContractError(ValueError):
    """Raised when a finite contract or certificate is malformed."""


# ---------------------------------------------------------------------------
# Bounded search
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SearchCertificate:
    bound: int
    found: bool
    witness: int
    tested: tuple[bool, ...]

    def verify(self, predicate: Callable[[int], bool]) -> bool:
        if self.bound < 0 or len(self.tested) != self.bound + 1:
            return False
        if tuple(bool(predicate(i)) for i in range(self.bound + 1)) != self.tested:
            return False
        hits = [i for i, ok in enumerate(self.tested) if ok]
        if not hits:
            return not self.found and self.witness == 0
        return self.found and self.witness == hits[0]


def least_bounded(predicate: Callable[[int], bool], bound: int) -> SearchCertificate:
    """Return the least witness in ``0..bound`` and a replayable trace.

    The convention for failure is ``found=False, witness=0``.  This makes the
    output total without pretending that 0 is a witness.
    """

    if bound < 0:
        raise ContractError("bounded search requires a nonnegative bound")
    tested = tuple(bool(predicate(i)) for i in range(bound + 1))
    for i, ok in enumerate(tested):
        if ok:
            cert = SearchCertificate(bound, True, i, tested)
            assert cert.verify(predicate)
            return cert
    cert = SearchCertificate(bound, False, 0, tested)
    assert cert.verify(predicate)
    return cert


# ---------------------------------------------------------------------------
# Monotone finite demand closure
# ---------------------------------------------------------------------------


Vector = tuple[int, ...]


def _vmax(*vectors: Sequence[int]) -> Vector:
    if not vectors:
        return ()
    n = len(vectors[0])
    if any(len(v) != n for v in vectors):
        raise ContractError("vectors have different dimensions")
    return tuple(max(v[i] for v in vectors) for i in range(n))


def _leq(a: Sequence[int], b: Sequence[int]) -> bool:
    return len(a) == len(b) and all(x <= y for x, y in zip(a, b))


@dataclass(frozen=True)
class ClosureCertificate:
    target: Vector
    bounds: Vector
    steps: tuple[Vector, ...]

    @property
    def result(self) -> Vector:
        return self.steps[-1]

    def verify(self, transform: Callable[[Vector], Vector]) -> bool:
        if not self.steps or len(self.target) != len(self.bounds):
            return False
        if any(x < 0 for x in self.target + self.bounds):
            return False
        if not _leq(self.target, self.bounds):
            return False
        if self.steps[0] != self.target:
            return False
        for current, nxt in zip(self.steps, self.steps[1:]):
            image = tuple(int(x) for x in transform(current))
            if len(image) != len(current) or any(x < 0 for x in image):
                return False
            expected = _vmax(self.target, current, image)
            if not _leq(expected, self.bounds) or nxt != expected:
                return False
        image = tuple(int(x) for x in transform(self.result))
        return _vmax(self.target, self.result, image) == self.result


def monotone_closure(
    target: Sequence[int],
    bounds: Sequence[int],
    transform: Callable[[Vector], Vector],
    *,
    check_monotone: bool = False,
) -> ClosureCertificate:
    """Compute the least inflationary closure above ``target`` in a finite box.

    We iterate ``d |-> max(target, d, transform(d))``.  Every nonstationary
    step strictly raises the coordinate sum, so at most
    ``1 + sum(bounds_i-target_i)`` states are needed.  When ``check_monotone``
    is true, monotonicity is exhaustively checked on the finite box; this is a
    diagnostic, not the intended proof method for large instances.
    """

    t = tuple(int(x) for x in target)
    b = tuple(int(x) for x in bounds)
    if len(t) != len(b) or any(x < 0 for x in t + b) or not _leq(t, b):
        raise ContractError("invalid target/bounds for demand closure")

    if check_monotone:
        points = list(product(*(range(limit + 1) for limit in b)))
        images: dict[Vector, Vector] = {}
        for p in points:
            q = tuple(int(x) for x in transform(tuple(p)))
            if len(q) != len(b) or any(x < 0 for x in q):
                raise ContractError("transform leaves the nonnegative vector space")
            images[tuple(p)] = q
        for p in points:
            for q in points:
                if _leq(p, q) and not _leq(images[tuple(p)], images[tuple(q)]):
                    raise ContractError(f"transform is not monotone: {p} <= {q}")

    current = t
    states = [current]
    fuel = 1 + sum(bi - ti for ti, bi in zip(t, b))
    for _ in range(fuel):
        image = tuple(int(x) for x in transform(current))
        if len(image) != len(current) or any(x < 0 for x in image):
            raise ContractError("transform returned an invalid vector")
        nxt = _vmax(t, current, image)
        if not _leq(nxt, b):
            raise ContractError(f"demand closure exceeds certified bounds: {nxt} > {b}")
        if nxt == current:
            cert = ClosureCertificate(t, b, tuple(states))
            if not cert.verify(transform):
                raise AssertionError("internal closure-certificate error")
            return cert
        states.append(nxt)
        current = nxt
    raise ContractError("finite-box closure failed to stabilize within its rank bound")


# ---------------------------------------------------------------------------
# Deterministic finite contract DAGs
# ---------------------------------------------------------------------------


DemandFunction = Callable[[int], Mapping[str, int]]
Evaluator = Callable[[Mapping[str, Any], int], Any]
LocalVerifier = Callable[[Mapping[str, Any], int, Any], bool]


@dataclass(frozen=True)
class DeterministicNode:
    name: str
    dependencies: tuple[str, ...]
    demand: DemandFunction
    evaluate: Evaluator
    verify: LocalVerifier
    description: str = ""


@dataclass(frozen=True)
class TraceEntry:
    node: str
    demand: int
    dependency_values: tuple[tuple[str, Any], ...]
    output: Any
    locally_valid: bool

    def dependency_map(self) -> dict[str, Any]:
        return dict(self.dependency_values)


@dataclass(frozen=True)
class DAGRun:
    goal: str
    requested_demand: int
    demands: tuple[tuple[str, int], ...]
    trace: tuple[TraceEntry, ...]
    output: Any

    def demand_map(self) -> dict[str, int]:
        return dict(self.demands)


@dataclass
class ContractDAG:
    nodes: Sequence[DeterministicNode]
    external_inputs: set[str] = field(default_factory=set)

    def __post_init__(self) -> None:
        names = [node.name for node in self.nodes]
        if len(names) != len(set(names)):
            raise ContractError("DAG node names must be unique")
        produced: set[str] = set(self.external_inputs)
        for node in self.nodes:
            missing = [d for d in node.dependencies if d not in produced]
            if missing:
                raise ContractError(
                    f"node {node.name!r} is not topologically ordered; missing {missing}"
                )
            produced.add(node.name)
        self._by_name = {node.name: node for node in self.nodes}

    def reverse_demands(self, goal: str, requested: int) -> dict[str, int]:
        if requested < 0:
            raise ContractError("demands must be nonnegative")
        if goal not in self._by_name and goal not in self.external_inputs:
            raise ContractError(f"unknown goal {goal!r}")
        required: dict[str, int] = {goal: requested}
        for node in reversed(self.nodes):
            if node.name not in required:
                continue
            local = dict(node.demand(required[node.name]))
            if set(local) != set(node.dependencies):
                raise ContractError(
                    f"demand function for {node.name!r} must mention exactly its dependencies"
                )
            for dep, amount in local.items():
                amount = int(amount)
                if amount < 0:
                    raise ContractError("demand functions must return nonnegative values")
                required[dep] = max(required.get(dep, 0), amount)
        return required

    def run(
        self,
        inputs: Mapping[str, Any],
        goal: str,
        requested: int = 0,
    ) -> DAGRun:
        if set(inputs) != self.external_inputs:
            raise ContractError(
                f"expected external inputs {sorted(self.external_inputs)}, got {sorted(inputs)}"
            )
        demands = self.reverse_demands(goal, requested)
        values: dict[str, Any] = dict(inputs)
        trace: list[TraceEntry] = []
        for node in self.nodes:
            if node.name not in demands:
                continue
            dep_values = {name: values[name] for name in node.dependencies}
            out = node.evaluate(dep_values, demands[node.name])
            valid = bool(node.verify(dep_values, demands[node.name], out))
            trace.append(
                TraceEntry(
                    node=node.name,
                    demand=demands[node.name],
                    dependency_values=tuple(dep_values.items()),
                    output=out,
                    locally_valid=valid,
                )
            )
            if not valid:
                raise ContractError(f"local contract failed at node {node.name!r}")
            values[node.name] = out
        if goal not in values:
            raise ContractError(f"goal {goal!r} was not evaluated")
        run = DAGRun(
            goal=goal,
            requested_demand=requested,
            demands=tuple(sorted(demands.items())),
            trace=tuple(trace),
            output=values[goal],
        )
        if not self.verify_run(inputs, run):
            raise AssertionError("internal DAG replay error")
        return run

    def verify_run(self, inputs: Mapping[str, Any], run: DAGRun) -> bool:
        try:
            expected_demands = self.reverse_demands(run.goal, run.requested_demand)
        except ContractError:
            return False
        if dict(run.demands) != dict(sorted(expected_demands.items())):
            return False
        values: dict[str, Any] = dict(inputs)
        entries = {entry.node: entry for entry in run.trace}
        for node in self.nodes:
            if node.name not in expected_demands:
                continue
            entry = entries.get(node.name)
            if entry is None or entry.demand != expected_demands[node.name]:
                return False
            dep_values = {name: values[name] for name in node.dependencies}
            if entry.dependency_map() != dep_values:
                return False
            expected_output = node.evaluate(dep_values, entry.demand)
            if expected_output != entry.output:
                return False
            if not entry.locally_valid or not node.verify(dep_values, entry.demand, entry.output):
                return False
            values[node.name] = entry.output
        return values.get(run.goal) == run.output


# ---------------------------------------------------------------------------
# Finite relational clouds and backward viability
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ViabilityCertificate:
    viable_indices: tuple[tuple[int, ...], ...]

    def layer(self, i: int) -> tuple[int, ...]:
        return self.viable_indices[i]


@dataclass
class FiniteCloudSystem:
    layers: Sequence[Sequence[Any]]
    compatible: Callable[[int, Any, Any], bool]
    terminal_good: Callable[[Any], bool]

    def __post_init__(self) -> None:
        if not self.layers or any(not layer for layer in self.layers):
            raise ContractError("a cloud system needs nonempty finite layers")

    def viability(self) -> ViabilityCertificate:
        viable: list[set[int]] = [set() for _ in self.layers]
        last = len(self.layers) - 1
        viable[last] = {
            j for j, candidate in enumerate(self.layers[last]) if self.terminal_good(candidate)
        }
        for i in range(last - 1, -1, -1):
            for j, candidate in enumerate(self.layers[i]):
                if any(
                    self.compatible(i, candidate, self.layers[i + 1][k])
                    for k in viable[i + 1]
                ):
                    viable[i].add(j)
        return ViabilityCertificate(tuple(tuple(sorted(v)) for v in viable))

    def least_path(self, start_index: int | None = None) -> tuple[Any, ...]:
        cert = self.viability()
        if not cert.layer(0):
            raise ContractError("the initial cloud has no viable candidate")
        current = min(cert.layer(0)) if start_index is None else start_index
        if current not in cert.layer(0):
            raise ContractError("requested start candidate is not viable")
        path = [self.layers[0][current]]
        for i in range(len(self.layers) - 1):
            choices = [
                k
                for k in cert.layer(i + 1)
                if self.compatible(i, self.layers[i][current], self.layers[i + 1][k])
            ]
            if not choices:
                raise AssertionError("viability table contains a dead end")
            current = min(choices)
            path.append(self.layers[i + 1][current])
        if not self.terminal_good(path[-1]):
            raise AssertionError("least viable path is not terminal-good")
        return tuple(path)

    def all_viable_paths(self, *, limit: int = 100_000) -> tuple[tuple[Any, ...], ...]:
        cert = self.viability()
        paths: list[tuple[Any, ...]] = []

        def visit(i: int, index: int, prefix: tuple[Any, ...]) -> None:
            if len(paths) >= limit:
                raise ContractError("viable-path enumeration exceeded its diagnostic limit")
            value = self.layers[i][index]
            prefix = prefix + (value,)
            if i + 1 == len(self.layers):
                if self.terminal_good(value):
                    paths.append(prefix)
                return
            for nxt in cert.layer(i + 1):
                if self.compatible(i, value, self.layers[i + 1][nxt]):
                    visit(i + 1, nxt, prefix)

        for start in cert.layer(0):
            visit(0, start, ())
        return tuple(paths)

    def observable_invariant(self, observable: Callable[[Any], Any]) -> tuple[bool, Any | None]:
        endpoints = [path[-1] for path in self.all_viable_paths()]
        if not endpoints:
            return False, None
        first = observable(endpoints[0])
        return all(observable(x) == first for x in endpoints), first

    def observable_diameter(
        self,
        observable: Callable[[Any], Fraction],
    ) -> Fraction:
        endpoints = [observable(path[-1]) for path in self.all_viable_paths()]
        if not endpoints:
            raise ContractError("cannot measure an empty viable family")
        return max(endpoints) - min(endpoints)


# ---------------------------------------------------------------------------
# Statement-admissibility diagnostics
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TheoremProfile:
    name: str
    fixed_or_clocked_programs: bool
    primitive_recursive_resource_bound: bool
    bounded_decidable_verifier: bool
    object_local_derivations: bool
    producer_supplied_or_proved: bool
    exact_selector_requested: bool = False
    collisions_possible: bool = False
    separation_gap_supplied: bool = False
    compactness_used: bool = False
    compactness_modulus_supplied: bool = False
    convergence_used: bool = False
    convergence_modulus_supplied: bool = False
    ineffective_constants_used: bool = False
    explicit_constants_supplied: bool = False
    finiteness_used: bool = False
    height_or_complete_list_supplied: bool = False


@dataclass(frozen=True)
class AdmissibilityReport:
    classification: str
    reasons: tuple[str, ...]
    repairs: tuple[str, ...]


def classify_profile(profile: TheoremProfile) -> AdmissibilityReport:
    reasons: list[str] = []
    repairs: list[str] = []

    if profile.exact_selector_requested and profile.collisions_possible and not profile.separation_gap_supplied:
        reasons.append("an exact branch selector is requested at possible collisions")
        repairs.append("return a finite cloud/quotient observable, or add an explicit separation gap")

    if not profile.fixed_or_clocked_programs:
        reasons.append("the statement relies on an unclocked universal evaluator")
        repairs.append("specialize the program at compile time or supply a primitive-recursive trace bound")

    if not profile.primitive_recursive_resource_bound:
        reasons.append("no primitive-recursive fuel or finite rank is supplied")
        repairs.append("supply a resource majorant, rank certificate, or finite horizon")

    if not profile.bounded_decidable_verifier:
        reasons.append("the advertised certificate is not checked by a bounded decidable relation")
        repairs.append("factor the claim into a finite certificate and a primitive-recursive checker")

    if profile.compactness_used and not profile.compactness_modulus_supplied:
        reasons.append("abstract compactness is used without a finite-net modulus")
        repairs.append("supply a covering/net modulus and a finite cover certificate")

    if profile.convergence_used and not profile.convergence_modulus_supplied:
        reasons.append("convergence is used without a modulus or fixed-precision reformulation")
        repairs.append("quantify precision last, supply a modulus, or state a metastable variant")

    if profile.ineffective_constants_used and not profile.explicit_constants_supplied:
        reasons.append("ineffective constants or exceptional data remain hidden")
        repairs.append("make the constants and exceptional cases explicit producer certificates")

    if profile.finiteness_used and not profile.height_or_complete_list_supplied:
        reasons.append("qualitative/cardinality finiteness supplies no stopping rule")
        repairs.append("supply a height bound or a complete finite list certificate")

    if not profile.producer_supplied_or_proved:
        reasons.append("the finite verifier is separated from an unproved certificate producer")
        repairs.append("state the iPRA theorem conditionally on the certificate, or prove a producer theorem")

    if not profile.object_local_derivations:
        reasons.append("local correctness exists only semantically, not as Prf PRAAx/NPrf derivations")
        repairs.append("implement local object-language proofs before invoking the contract compiler")

    if not reasons:
        return AdmissibilityReport(
            "object-internalizable",
            ("all finite resources, verifiers, producers, and local derivations are explicit",),
            (),
        )

    selector_only = (
        profile.exact_selector_requested
        and profile.collisions_possible
        and not profile.separation_gap_supplied
    )
    hard_resource = (
        not profile.fixed_or_clocked_programs
        or not profile.primitive_recursive_resource_bound
        or not profile.bounded_decidable_verifier
    )
    missing_producer = (
        not profile.producer_supplied_or_proved
        or (profile.ineffective_constants_used and not profile.explicit_constants_supplied)
        or (profile.finiteness_used and not profile.height_or_complete_list_supplied)
    )

    if selector_only and not hard_resource and not missing_producer:
        classification = "reformulate-relationally"
    elif hard_resource:
        classification = "not-yet-admissible"
    else:
        classification = "conditional-on-producer"
    return AdmissibilityReport(classification, tuple(reasons), tuple(dict.fromkeys(repairs)))


# ---------------------------------------------------------------------------
# Small serialization helpers
# ---------------------------------------------------------------------------


def json_value(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, tuple):
        return [json_value(v) for v in value]
    if isinstance(value, list):
        return [json_value(v) for v in value]
    if isinstance(value, dict):
        return {str(k): json_value(v) for k, v in value.items()}
    if hasattr(value, "__dict__"):
        return {k: json_value(v) for k, v in value.__dict__.items()}
    return value
