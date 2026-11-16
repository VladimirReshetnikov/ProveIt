"""Finite reference algorithms for DARC-iPRA.

These routines model the *metalevel* analyses described in the paper:
least demand closure, witness liveness, bounded strategy certificates,
trace checking, and finite relational viability.  They deliberately do not
implement an iPRA proof checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Any, Callable, Iterable, Mapping, Sequence


class DARCError(ValueError):
    """Raised when a finite DARC artifact is malformed."""


@dataclass(frozen=True)
class ResourceShape:
    """A finite product of chains ``0..cap[i]`` with named coordinates."""

    names: tuple[str, ...]
    caps: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.names) != len(self.caps):
            raise DARCError("resource names and capacities must have equal length")
        if len(set(self.names)) != len(self.names):
            raise DARCError("resource names must be unique")
        if any(c < 0 for c in self.caps):
            raise DARCError("resource capacities must be nonnegative")

    @property
    def dimension(self) -> int:
        return len(self.names)

    @property
    def max_rank(self) -> int:
        return sum(self.caps)

    def zero(self) -> "Demand":
        return Demand(self, (0,) * self.dimension)

    def demand(self, values: Mapping[str, int] | Sequence[int]) -> "Demand":
        if isinstance(values, Mapping):
            unknown = set(values).difference(self.names)
            if unknown:
                raise DARCError(f"unknown resource coordinates: {sorted(unknown)}")
            row = tuple(int(values.get(name, 0)) for name in self.names)
        else:
            row = tuple(int(v) for v in values)
        return Demand(self, row)

    def all_demands(self) -> Iterable["Demand"]:
        for values in product(*(range(c + 1) for c in self.caps)):
            yield Demand(self, tuple(values))


@dataclass(frozen=True)
class Demand:
    shape: ResourceShape
    values: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.values) != self.shape.dimension:
            raise DARCError("demand has the wrong dimension")
        for name, value, cap in zip(self.shape.names, self.values, self.shape.caps):
            if not 0 <= value <= cap:
                raise DARCError(f"coordinate {name!r}={value} is outside 0..{cap}")

    def __getitem__(self, name: str) -> int:
        try:
            return self.values[self.shape.names.index(name)]
        except ValueError as exc:
            raise KeyError(name) from exc

    def as_dict(self) -> dict[str, int]:
        return dict(zip(self.shape.names, self.values))

    @property
    def rank(self) -> int:
        return sum(self.values)

    def le(self, other: "Demand") -> bool:
        self._same_shape(other)
        return all(a <= b for a, b in zip(self.values, other.values))

    def join(self, other: "Demand") -> "Demand":
        self._same_shape(other)
        return Demand(self.shape, tuple(max(a, b) for a, b in zip(self.values, other.values)))

    def meet(self, other: "Demand") -> "Demand":
        self._same_shape(other)
        return Demand(self.shape, tuple(min(a, b) for a, b in zip(self.values, other.values)))

    def with_updates(self, updates: Mapping[str, int]) -> "Demand":
        data = self.as_dict()
        for name, value in updates.items():
            if name not in data:
                raise DARCError(f"unknown resource coordinate: {name}")
            data[name] = max(data[name], int(value))
        return self.shape.demand(data)

    def _same_shape(self, other: "Demand") -> None:
        if self.shape != other.shape:
            raise DARCError("demand shapes do not match")


@dataclass(frozen=True)
class ThresholdRule:
    """A monotone Horn-style transfer clause on resource demands.

    When every trigger coordinate is at least its threshold, all requirements
    are joined into the next demand state.
    """

    triggers: tuple[tuple[str, int], ...]
    requirements: tuple[tuple[str, int], ...]
    label: str = ""

    @classmethod
    def make(
        cls,
        triggers: Mapping[str, int],
        requirements: Mapping[str, int],
        label: str = "",
    ) -> "ThresholdRule":
        return cls(tuple(sorted(triggers.items())), tuple(sorted(requirements.items())), label)

    def fires(self, demand: Demand) -> bool:
        return all(demand[name] >= threshold for name, threshold in self.triggers)

    def apply(self, demand: Demand) -> Demand:
        return demand.with_updates(dict(self.requirements)) if self.fires(demand) else demand


@dataclass(frozen=True)
class DemandClosure:
    seed: Demand
    fixed_point: Demand
    history: tuple[Demand, ...]
    fired_rules: tuple[tuple[str, ...], ...]

    @property
    def strict_steps(self) -> int:
        return sum(a != b for a, b in zip(self.history, self.history[1:]))


class DemandNetwork:
    """A finite monotone transfer network.

    The transfer is the join of all threshold rules that fire.  Iterating
    ``d -> d join transfer(d)`` computes the least prefixed point above a seed.
    """

    def __init__(self, shape: ResourceShape, rules: Sequence[ThresholdRule]) -> None:
        self.shape = shape
        self.rules = tuple(rules)
        self._validate_rules()

    def _validate_rules(self) -> None:
        known = set(self.shape.names)
        caps = dict(zip(self.shape.names, self.shape.caps))
        for rule in self.rules:
            for name, level in (*rule.triggers, *rule.requirements):
                if name not in known:
                    raise DARCError(f"rule {rule.label!r} uses unknown coordinate {name!r}")
                if not 0 <= level <= caps[name]:
                    raise DARCError(
                        f"rule {rule.label!r} uses level {level} outside {name}=0..{caps[name]}"
                    )

    def transfer(self, demand: Demand) -> tuple[Demand, tuple[str, ...]]:
        if demand.shape != self.shape:
            raise DARCError("network and demand shapes do not match")
        result = demand
        fired: list[str] = []
        for rule in self.rules:
            if rule.fires(demand):
                next_result = result.with_updates(dict(rule.requirements))
                if next_result != result or rule.label:
                    fired.append(rule.label or repr(rule))
                result = next_result
        return result, tuple(fired)

    def closure(self, seed: Demand) -> DemandClosure:
        if seed.shape != self.shape:
            raise DARCError("network and seed shapes do not match")
        history = [seed]
        fired_history: list[tuple[str, ...]] = []
        current = seed
        # Every strict step increases rank by at least one, so max_rank + 1
        # evaluations suffice even when the seed is nonzero.
        for _ in range(self.shape.max_rank + 1):
            transferred, fired = self.transfer(current)
            nxt = current.join(transferred)
            fired_history.append(fired)
            if nxt == current:
                return DemandClosure(seed, current, tuple(history), tuple(fired_history))
            if nxt.rank <= current.rank:
                raise DARCError("non-strict demand update did not stabilize")
            history.append(nxt)
            current = nxt
        raise DARCError("demand closure exceeded the finite-chain rank bound")

    def is_prefixed(self, demand: Demand) -> bool:
        transferred, _ = self.transfer(demand)
        return transferred.le(demand)

    def check_monotone_exhaustively(self, max_comparable_pairs: int = 200_000) -> bool:
        """Check monotonicity on every comparable pair of demand states.

        A product chain with coordinate cap ``c`` has ``(c+1)(c+2)/2``
        ordered pairs ``a <= b`` in that coordinate.  Using the product of
        those counts avoids rejecting moderate lattices merely because the
        square of the total state count is large.
        """

        pair_count = 1
        for cap in self.shape.caps:
            pair_count *= (cap + 1) * (cap + 2) // 2
        if pair_count > max_comparable_pairs:
            raise DARCError(
                f"exhaustive monotonicity check would inspect {pair_count} comparable pairs"
            )
        for a in self.shape.all_demands():
            ta, _ = self.transfer(a)
            ranges = [range(value, cap + 1) for value, cap in zip(a.values, self.shape.caps)]
            for values in product(*ranges):
                b = Demand(self.shape, tuple(values))
                tb, _ = self.transfer(b)
                if not ta.le(tb):
                    return False
        return True

    def check_least(self, closure: DemandClosure) -> bool:
        """Exhaustively verify leastness on small finite networks."""
        for candidate in self.shape.all_demands():
            if closure.seed.le(candidate) and self.is_prefixed(candidate):
                if not closure.fixed_point.le(candidate):
                    return False
        return True


def bounded_least(bound: int, predicate: Callable[[int], bool]) -> int:
    """Return the least witness below ``bound``, or ``bound`` if none exists."""
    if bound < 0:
        raise DARCError("bound must be nonnegative")
    for i in range(bound):
        if predicate(i):
            return i
    return bound


# ---------------------------------------------------------------------------
# Fixed bounded formulas and strategy certificates
# ---------------------------------------------------------------------------


class QFormula:
    def evaluate(self, env: Mapping[str, int]) -> bool:
        raise NotImplementedError


@dataclass(frozen=True)
class Atom(QFormula):
    name: str
    predicate: Callable[[Mapping[str, int]], bool]

    def evaluate(self, env: Mapping[str, int]) -> bool:
        return bool(self.predicate(env))


@dataclass(frozen=True)
class QAnd(QFormula):
    left: QFormula
    right: QFormula

    def evaluate(self, env: Mapping[str, int]) -> bool:
        return self.left.evaluate(env) and self.right.evaluate(env)


@dataclass(frozen=True)
class QOr(QFormula):
    left: QFormula
    right: QFormula

    def evaluate(self, env: Mapping[str, int]) -> bool:
        return self.left.evaluate(env) or self.right.evaluate(env)


@dataclass(frozen=True)
class ExistsBounded(QFormula):
    var: str
    bound: int | Callable[[Mapping[str, int]], int]
    body: QFormula

    def actual_bound(self, env: Mapping[str, int]) -> int:
        value = self.bound(env) if callable(self.bound) else self.bound
        if value < 0:
            raise DARCError("bounded quantifier has a negative bound")
        return int(value)

    def evaluate(self, env: Mapping[str, int]) -> bool:
        return any(self.body.evaluate({**env, self.var: i}) for i in range(self.actual_bound(env)))


@dataclass(frozen=True)
class ForallBounded(QFormula):
    var: str
    bound: int | Callable[[Mapping[str, int]], int]
    body: QFormula

    def actual_bound(self, env: Mapping[str, int]) -> int:
        value = self.bound(env) if callable(self.bound) else self.bound
        if value < 0:
            raise DARCError("bounded quantifier has a negative bound")
        return int(value)

    def evaluate(self, env: Mapping[str, int]) -> bool:
        return all(self.body.evaluate({**env, self.var: i}) for i in range(self.actual_bound(env)))


def build_strategy(formula: QFormula, env: Mapping[str, int] | None = None) -> Any:
    """Build a canonical certificate for a true positive bounded formula.

    The certificate language is intentionally small: atoms carry their name,
    conjunctions carry both branches, disjunctions select the leftmost true
    branch, existential quantifiers select the least true witness, and
    universal quantifiers carry one certificate per bounded input.
    """

    env = {} if env is None else dict(env)
    if isinstance(formula, Atom):
        if not formula.evaluate(env):
            raise DARCError(f"false atom {formula.name!r} has no winning certificate")
        return {"tag": "atom", "name": formula.name}
    if isinstance(formula, QAnd):
        return {
            "tag": "and",
            "left": build_strategy(formula.left, env),
            "right": build_strategy(formula.right, env),
        }
    if isinstance(formula, QOr):
        if formula.left.evaluate(env):
            return {"tag": "or", "side": "left", "sub": build_strategy(formula.left, env)}
        if formula.right.evaluate(env):
            return {"tag": "or", "side": "right", "sub": build_strategy(formula.right, env)}
        raise DARCError("false disjunction has no winning certificate")
    if isinstance(formula, ExistsBounded):
        bound = formula.actual_bound(env)
        witness = bounded_least(bound, lambda i: formula.body.evaluate({**env, formula.var: i}))
        if witness == bound:
            raise DARCError("false existential has no winning certificate")
        return {
            "tag": "exists",
            "var": formula.var,
            "witness": witness,
            "sub": build_strategy(formula.body, {**env, formula.var: witness}),
        }
    if isinstance(formula, ForallBounded):
        bound = formula.actual_bound(env)
        branches = []
        for i in range(bound):
            branches.append(build_strategy(formula.body, {**env, formula.var: i}))
        return {"tag": "forall", "var": formula.var, "branches": branches}
    raise TypeError(f"unsupported formula: {type(formula).__name__}")


def check_strategy(formula: QFormula, certificate: Any, env: Mapping[str, int] | None = None) -> bool:
    env = {} if env is None else dict(env)
    if not isinstance(certificate, Mapping):
        return False
    if isinstance(formula, Atom):
        return (
            certificate.get("tag") == "atom"
            and certificate.get("name") == formula.name
            and formula.evaluate(env)
        )
    if isinstance(formula, QAnd):
        return (
            certificate.get("tag") == "and"
            and check_strategy(formula.left, certificate.get("left"), env)
            and check_strategy(formula.right, certificate.get("right"), env)
        )
    if isinstance(formula, QOr):
        if certificate.get("tag") != "or":
            return False
        side = certificate.get("side")
        if side == "left":
            return check_strategy(formula.left, certificate.get("sub"), env)
        if side == "right":
            return check_strategy(formula.right, certificate.get("sub"), env)
        return False
    if isinstance(formula, ExistsBounded):
        if certificate.get("tag") != "exists" or certificate.get("var") != formula.var:
            return False
        witness = certificate.get("witness")
        if not isinstance(witness, int) or not 0 <= witness < formula.actual_bound(env):
            return False
        return check_strategy(
            formula.body,
            certificate.get("sub"),
            {**env, formula.var: witness},
        )
    if isinstance(formula, ForallBounded):
        if certificate.get("tag") != "forall" or certificate.get("var") != formula.var:
            return False
        branches = certificate.get("branches")
        bound = formula.actual_bound(env)
        if not isinstance(branches, Sequence) or isinstance(branches, (str, bytes)):
            return False
        if len(branches) != bound:
            return False
        return all(
            check_strategy(formula.body, branches[i], {**env, formula.var: i})
            for i in range(bound)
        )
    return False


# ---------------------------------------------------------------------------
# Trace reflection and finite relational viability
# ---------------------------------------------------------------------------


def run_trace(initial: Any, step: Callable[[Any], Any], fuel: int) -> list[Any]:
    if fuel < 0:
        raise DARCError("trace fuel must be nonnegative")
    states = [initial]
    for _ in range(fuel):
        states.append(step(states[-1]))
    return states


def check_trace(
    states: Sequence[Any],
    step: Callable[[Any], Any],
    invariant: Callable[[Any], bool] | None = None,
) -> bool:
    if not states:
        return False
    if invariant is not None and not all(invariant(state) for state in states):
        return False
    return all(states[i + 1] == step(states[i]) for i in range(len(states) - 1))


@dataclass(frozen=True)
class ViabilityResult:
    viable_layers: tuple[tuple[Any, ...], ...]
    least_path: tuple[Any, ...] | None


def backward_viability(
    layers: Sequence[Sequence[Any]],
    edge: Callable[[int, Any, Any], bool],
    start: Any | None = None,
    key: Callable[[Any], Any] = lambda x: x,
) -> ViabilityResult:
    """Prune a finite layered relation backward and choose a least path.

    ``edge(i, x, y)`` relates layer ``i`` to layer ``i + 1``.
    """

    if not layers:
        raise DARCError("viability requires at least one layer")
    viable: list[list[Any]] = [list(dict.fromkeys(layer)) for layer in layers]
    for i in range(len(viable) - 2, -1, -1):
        viable[i] = [
            x for x in viable[i] if any(edge(i, x, y) for y in viable[i + 1])
        ]
    viable_t = tuple(tuple(sorted(layer, key=key)) for layer in viable)
    if start is None:
        if not viable_t[0]:
            return ViabilityResult(viable_t, None)
        current = viable_t[0][0]
    else:
        if start not in viable_t[0]:
            return ViabilityResult(viable_t, None)
        current = start
    path = [current]
    for i in range(len(viable_t) - 1):
        choices = [y for y in viable_t[i + 1] if edge(i, current, y)]
        if not choices:
            # This cannot happen for a viable node, but guard against a bad edge predicate.
            return ViabilityResult(viable_t, None)
        current = min(choices, key=key)
        path.append(current)
    return ViabilityResult(viable_t, tuple(path))


# ---------------------------------------------------------------------------
# Helpers for DARC artifact generation
# ---------------------------------------------------------------------------


def selected_coordinates(demand: Demand, prefix: str) -> list[str]:
    return [name for name, value in demand.as_dict().items() if name.startswith(prefix) and value > 0]


def closure_report(network: DemandNetwork, seed: Demand) -> dict[str, Any]:
    closure = network.closure(seed)
    try:
        monotone_exhaustive: bool | None = network.check_monotone_exhaustively()
        monotone_note = "all comparable pairs checked"
    except DARCError as exc:
        # Threshold rules are monotone by construction: increasing a demand can
        # only enable more rules, and every update is a coordinatewise join.
        monotone_exhaustive = None
        monotone_note = f"symbolic threshold-rule argument; {exc}"
    return {
        "seed": closure.seed.as_dict(),
        "fixed_point": closure.fixed_point.as_dict(),
        "rank_bound": network.shape.max_rank,
        "strict_steps": closure.strict_steps,
        "history": [state.as_dict() for state in closure.history],
        "fired_rules": [list(labels) for labels in closure.fired_rules],
        "least_prefixed_point_checked": network.check_least(closure),
        "monotone_checked": True,
        "monotone_exhaustive": monotone_exhaustive,
        "monotone_note": monotone_note,
        "live_certificates": selected_coordinates(closure.fixed_point, "cert:"),
        "required_guards": selected_coordinates(closure.fixed_point, "guard:"),
        "residuals": selected_coordinates(closure.fixed_point, "residual:"),
    }
