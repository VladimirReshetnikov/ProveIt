"""Executable witness for the tied-seed B term-boundedness theorem.

This is an illustration of a standard-model structural proof, not an iPRA
proof checker and not a search for all possible relational interpretations.
The environment of a body is (old_counter, previous_state, *outer_values).
Every computed bound is nondecreasing and primitive recursive in its
selected input; a None source denotes a uniform constant bound.
"""
from dataclasses import dataclass
from typing import Callable, Optional


@dataclass(frozen=True)
class Var:
    index: int


@dataclass(frozen=True)
class Zero:
    pass


@dataclass(frozen=True)
class B:
    counter: object
    body: object


@dataclass(frozen=True)
class Bound:
    source: Optional[int]
    function: Callable[[int], int]

    def at(self, environment):
        return self.function(0 if self.source is None else environment[self.source])


def evaluate(term, environment=()):
    if isinstance(term, Zero):
        return 0
    if isinstance(term, Var):
        return environment[term.index]
    count = evaluate(term.counter, environment)
    state = 1 + evaluate(term.body, (0, 0) + tuple(environment))
    for counter in range(count):
        state = evaluate(term.body, (counter, state) + tuple(environment))
    return state


def compile_bound(term):
    if isinstance(term, Zero):
        return Bound(None, lambda _: 0)
    if isinstance(term, Var):
        return Bound(term.index, lambda x: x)
    body = compile_bound(term.body)
    h = body.function
    if body.source is None:
        constant = h(0) + 1
        return Bound(None, lambda _: constant)
    if body.source >= 2:
        return Bound(body.source - 2, lambda x: h(x) + 1)
    if body.source == 0:
        # Monotonicity gives the simpler envelope 1 + H(m).
        k = lambda m: h(m) + 1
    else:
        def k(m):
            value = h(0) + 1
            for _ in range(m):
                value = max(value, h(value))
            return value
    count = compile_bound(term.counter)
    if count.source is None:
        constant = k(count.function(0))
        return Bound(None, lambda _: constant)
    return Bound(count.source, lambda x: k(count.function(x)))


def shift(term, amount, cutoff=0):
    """Capture-free insertion of fresh bound coordinates."""
    if isinstance(term, Zero):
        return term
    if isinstance(term, Var):
        return Var(term.index + amount if term.index >= cutoff else term.index)
    return B(shift(term.counter, amount, cutoff),
             shift(term.body, amount, cutoff + 2))


def successor(term):
    return B(Zero(), shift(term, 2))


def delta(control, value):
    return B(control, shift(value, 2))


def bounce(term):
    return B(term, Var(0))


def predecessor(term):
    return bounce(delta(term, term))


def mask(control, value):
    # Bound slots of this outer B are u=0 and v=1.
    update = delta(shift(control, 2), Var(1))
    return predecessor(predecessor(B(value, update)))


def finite_diagnostic(limit=6):
    """Check concrete transcriptions of all bound-compiler branches."""
    import itertools
    terms = {
        "constant_body": B(Var(0), Zero()),
        "passive_body": delta(Var(0), Var(1)),
        "counter_body": bounce(Var(0)),
        "state_body": B(Var(0), successor(Var(1))),
        "predecessor": predecessor(Var(0)),
        "mask": mask(Var(0), Var(1)),
    }
    checked = 0
    summary = {}
    for name, term in terms.items():
        bound = compile_bound(term)
        for environment in itertools.product(range(limit + 1), repeat=2):
            value = evaluate(term, environment)
            assert value <= bound.at(environment), (name, environment, value)
            if name == "predecessor":
                assert value == max(environment[0] - 1, 0)
            if name == "mask":
                assert value == (environment[1] if environment[0] == 0 else 0)
            checked += 1
        summary[name] = {"bounding_coordinate": bound.source}
    return {"checked_instances": checked, "terms": summary}


if __name__ == "__main__":
    import json
    print(json.dumps(finite_diagnostic(), indent=2))
