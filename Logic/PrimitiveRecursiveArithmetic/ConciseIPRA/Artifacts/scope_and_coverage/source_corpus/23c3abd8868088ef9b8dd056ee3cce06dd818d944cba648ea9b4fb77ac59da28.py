"""Terms for the three-schema 0,G,J numerical presentation.

The primitive syntax is Zero, Free, Bound, Gate and Iterate. Successor,
predecessor, selection and initialized iteration are finite term builders.
Iterate binds Bound(0) only in its body. De Bruijn indices and lifting make
substitution capture avoiding. The evaluator is a standard-number model,
not an iPRA proof checker. The symbolic normalizer uses only the three
computation schemas; it neither proves induction nor proves equivalence.
"""
from dataclasses import dataclass
from functools import lru_cache
from typing import Mapping, Union


@dataclass(frozen=True)
class Zero:
    pass


@dataclass(frozen=True)
class Free:
    name: str


@dataclass(frozen=True)
class Bound:
    index: int


@dataclass(frozen=True)
class Gate:
    control: "Term"
    fallback: "Term"


@dataclass(frozen=True)
class Iterate:
    counter: "Term"
    body: "Term"


Term = Union[Zero, Free, Bound, Gate, Iterate]
ZERO = Zero()


def validate(term: Term, depth: int = 0) -> None:
    """Reject ill-scoped bound variables and malformed constructor fields."""
    if type(depth) is not int or depth < 0:
        raise ValueError("depth must be a nonnegative integer")
    if type(term) is Zero:
        return
    if type(term) is Free:
        if type(term.name) is not str or not term.name:
            raise ValueError("a free variable needs a nonempty string name")
        return
    if type(term) is Bound:
        if type(term.index) is not int or not 0 <= term.index < depth:
            raise ValueError("dangling or malformed bound index")
        return
    if type(term) is Gate:
        validate(term.control, depth)
        validate(term.fallback, depth)
        return
    if type(term) is Iterate:
        validate(term.counter, depth)
        validate(term.body, depth + 1)
        return
    raise TypeError("not a numerical term")


def free_names(term: Term) -> set[str]:
    if isinstance(term, Free):
        return {term.name}
    if isinstance(term, Gate):
        return free_names(term.control) | free_names(term.fallback)
    if isinstance(term, Iterate):
        return free_names(term.counter) | free_names(term.body)
    return set()


def lift(term: Term, amount: int = 1, cutoff: int = 0) -> Term:
    """Lift ambient de Bruijn references through newly inserted binders."""
    if isinstance(term, Bound):
        return Bound(term.index + amount) if term.index >= cutoff else term
    if isinstance(term, Gate):
        return Gate(lift(term.control, amount, cutoff),
                    lift(term.fallback, amount, cutoff))
    if isinstance(term, Iterate):
        return Iterate(lift(term.counter, amount, cutoff),
                       lift(term.body, amount, cutoff + 1))
    return term


def replace_free(term: Term, name: str, image: Term, depth: int = 0) -> Term:
    """Replace a free name; inserted ambient references cannot be captured."""
    if isinstance(term, Free) and term.name == name:
        return lift(image, depth)
    if isinstance(term, Gate):
        return Gate(replace_free(term.control, name, image, depth),
                    replace_free(term.fallback, name, image, depth))
    if isinstance(term, Iterate):
        return Iterate(replace_free(term.counter, name, image, depth),
                       replace_free(term.body, name, image, depth + 1))
    return term


def abstract(term: Term, name: str, depth: int = 0) -> Term:
    """Bind free occurrences of name while lifting older ambient references."""
    if isinstance(term, Free) and term.name == name:
        return Bound(depth)
    if isinstance(term, Bound):
        return Bound(term.index + 1) if term.index >= depth else term
    if isinstance(term, Gate):
        return Gate(abstract(term.control, name, depth),
                    abstract(term.fallback, name, depth))
    if isinstance(term, Iterate):
        return Iterate(abstract(term.counter, name, depth),
                       abstract(term.body, name, depth + 1))
    return term


def instantiate(body: Term, image: Term, depth: int = 0) -> Term:
    """Open one binder and decrement references to the outer environment."""
    if isinstance(body, Bound):
        if body.index == depth:
            return lift(image, depth)
        return Bound(body.index - 1) if body.index > depth else body
    if isinstance(body, Gate):
        return Gate(instantiate(body.control, image, depth),
                    instantiate(body.fallback, image, depth))
    if isinstance(body, Iterate):
        return Iterate(instantiate(body.counter, image, depth),
                       instantiate(body.body, image, depth + 1))
    return body


def bind_iteration(counter: Term, name: str, body: Term) -> Term:
    """Bind name in body only. It stays free in the numerical counter."""
    return Iterate(counter, abstract(body, name))


def constant_iteration(counter: Term, value: Term) -> Term:
    return Iterate(counter, lift(value))


def successor(term: Term) -> Term:
    return Gate(ZERO, term)


def numeral(value: int) -> Term:
    if type(value) is not int or value < 0:
        raise ValueError("a numeral must be a nonnegative integer")
    result = ZERO
    for _ in range(value):
        result = successor(result)
    return result


def bounce(term: Term) -> Term:
    return Gate(term, ZERO)


def predecessor(term: Term) -> Term:
    return constant_iteration(term, bounce(term))


def select(control: Term, at_zero: Term, at_positive: Term) -> Term:
    twice = successor(successor(at_positive))
    return bounce(Gate(constant_iteration(control, twice), at_zero))


def fresh_name(terms: tuple[Term, ...], stem: str = "_state") -> str:
    forbidden = set().union(*(free_names(t) for t in terms))
    name = stem
    while name in forbidden:
        name += "_"
    return name


def initialized(counter: Term, seed: Term, update: Term,
                state_name: str = "v") -> Term:
    """Compile h^counter(seed); free state_name occurrences denote h's state.

    All other free names are passive. counter and seed are outside h's
    state binder; occurrences of state_name there remain free. The fresh
    loading marker cannot coincide with any passive name.
    """
    marker = fresh_name((counter, seed, update))
    state = Free(marker)
    next_value = replace_free(update, state_name, predecessor(state))
    load_or_step = select(state, successor(seed), successor(next_value))
    encoded = bind_iteration(successor(counter), marker, load_or_step)
    return predecessor(encoded)


def evaluate(term: Term, parameters: Mapping[str, int] | None = None) -> int:
    """Evaluate the primitive grammar in the intended standard model."""
    validate(term)
    values = dict(parameters or {})
    for name in free_names(term):
        value = values.get(name)
        if type(value) is not int or value < 0:
            raise ValueError("all free parameters need nonnegative integer values")

    @lru_cache(maxsize=None)
    def run(node: Term, environment: tuple[int, ...]) -> int:
        if isinstance(node, Zero):
            return 0
        if isinstance(node, Free):
            return values[node.name]
        if isinstance(node, Bound):
            return environment[node.index]
        if isinstance(node, Gate):
            x = run(node.control, environment)
            y = run(node.fallback, environment)
            return y + 1 if x == 0 else x - 1
        if isinstance(node, Iterate):
            count = run(node.counter, environment)
            state = 0
            for _ in range(count):
                state = run(node.body, (state,) + environment)
            return state
        raise TypeError("not a numerical term")

    return run(term, ())


def normalize(term: Term, max_rewrites: int = 10000) -> tuple[Term, int]:
    """Normalize by G-cancellation, J0 and JS only, with a finite budget.

    A literal successor is Gate(Zero(),n). This checker does not know any
    algebraic identity beyond those three oriented computation schemas.
    """
    rewrites = 0

    def step(node: Term) -> Term:
        nonlocal rewrites
        if isinstance(node, Gate):
            node = Gate(step(node.control), step(node.fallback))
            if isinstance(node.control, Gate) and isinstance(node.control.control, Zero):
                rewrites += 1
                if rewrites > max_rewrites:
                    raise ValueError("rewrite budget exhausted")
                return step(node.control.fallback)
        elif isinstance(node, Iterate):
            node = Iterate(step(node.counter), step(node.body))
            if isinstance(node.counter, Zero):
                rewrites += 1
                if rewrites > max_rewrites:
                    raise ValueError("rewrite budget exhausted")
                return ZERO
            if isinstance(node.counter, Gate) and isinstance(node.counter.control, Zero):
                rewrites += 1
                if rewrites > max_rewrites:
                    raise ValueError("rewrite budget exhausted")
                earlier = Iterate(node.counter.fallback, node.body)
                return step(instantiate(node.body, earlier))
        return node

    return step(term), rewrites


def encode(term: Term):
    """A plain JSON representation for inspecting primitive-only expansions."""
    if isinstance(term, Zero):
        return ["0"]
    if isinstance(term, Free):
        return ["free", term.name]
    if isinstance(term, Bound):
        return ["bound", term.index]
    if isinstance(term, Gate):
        return ["G", encode(term.control), encode(term.fallback)]
    if isinstance(term, Iterate):
        return ["J", encode(term.counter), encode(term.body)]
    raise TypeError("not a numerical term")
