"""Exact standard-N evaluation of the scalar successor-seeded construction.

The sole recursion operation is R(n, a, h) = h^n(a + 1).  Every public
arithmetic abbreviation below is implemented from R and earlier finite
abbreviations.  Python integers and loops interpret the intended standard
model; this is not a proof assistant and does not establish internal
derivability or correctness in nonstandard models.

Memoization reuses evaluated subterms without replacing their definitions
by their expected arithmetic meanings.  In particular, Pred does NOT call
subtraction, V does NOT compare its arguments, and I does NOT directly
iterate from its requested initializer.  The exact construction is costly;
the accompanying tests deliberately keep counters and outputs small.
"""

from functools import cache
from typing import Callable

Update = Callable[[int], int]


@cache
def R(n: int, a: int, h: Update) -> int:
    """Interpret the primitive recursor; h is a fixed finite update."""
    if type(n) is not int or type(a) is not int or n < 0 or a < 0:
        raise ValueError("R expects natural counters and initializers")
    value = a + 1
    for _ in range(n):
        value = h(value)
        if type(value) is not int or value < 0:
            raise ValueError("an update left the natural-number domain")
    return value


def zero_update(_: int) -> int:
    return 0


@cache
def S(a: int) -> int:
    return R(0, a, zero_update)


@cache
def constant(a: int) -> Update:
    def update(_: int) -> int:
        return a
    return update


@cache
def C(n: int, a: int, b: int) -> int:
    """Shifted selector: C(0,a,b)=S(a), C(S(n),a,b)=b."""
    return R(n, a, constant(b))


@cache
def Z(n: int) -> int:
    return C(n, 0, 0)


@cache
def even(n: int) -> int:
    return R(n, 0, Z)


@cache
def boolean_and(a: int, b: int) -> int:
    return Z(C(a, 0, Z(b)))


@cache
def q(u: int) -> int:
    return boolean_and(even(u), Z(Z(u)))


@cache
def pulse(n: int) -> int:
    return R(n, S(0), q)


@cache
def one_indicator(n: int) -> int:
    return Z(even(pulse(n)))


@cache
def swap_update(u: int) -> int:
    return C(one_indicator(u), C(u, 0, u), 0)


@cache
def J(n: int) -> int:
    """The derived involution swapping 0 and 1."""
    return R(n, 0, swap_update)


@cache
def conjugate(h: Update) -> Update:
    @cache
    def update(u: int) -> int:
        return J(h(J(u)))
    return update


@cache
def K(n: int, h: Update) -> int:
    """Derived zero-start iteration, evaluated through its R expression."""
    return J(R(n, 0, conjugate(h)))


@cache
def T(x: int, y: int) -> int:
    return R(y, x, S)


@cache
def twice_successor(u: int) -> int:
    return S(S(u))


@cache
def d(n: int) -> int:
    return K(n, twice_successor)


@cache
def D(n: int) -> int:
    return T(n, n)


@cache
def A3(n: int) -> int:
    return T(D(n), n)


@cache
def N(n: int) -> int:
    return Z(even(n))


@cache
def cycle3_update(u: int) -> int:
    return C(u, 0, C(even(u), S(0), 0))


@cache
def M(n: int) -> int:
    return K(n, cycle3_update)


@cache
def ramp_update(u: int) -> int:
    return T(u, M(u))


@cache
def F(n: int) -> int:
    return K(n, ramp_update)


@cache
def H(u: int) -> int:
    return C(even(u), F(u), u)


@cache
def E(n: int) -> int:
    return K(n, D)


@cache
def V(x: int, y: int) -> int:
    """The strict comparator, evaluated through its exact scalar orbit."""
    return even(R(y, d(E(x)), H))


@cache
def saturation_update(m: int) -> Update:
    @cache
    def update(u: int) -> int:
        return C(Z(V(u, m)), u, u)
    return update


@cache
def W(t: int, m: int) -> int:
    return K(t, saturation_update(m))


@cache
def predecessor_update(m: int) -> Update:
    @cache
    def update(u: int) -> int:
        return C(Z(V(S(u), m)), u, u)
    return update


@cache
def Pred(m: int) -> int:
    return K(m, predecessor_update(m))


@cache
def lifted_update(h: Update) -> Update:
    @cache
    def update(u: int) -> int:
        return S(h(Pred(u)))
    return update


@cache
def I(n: int, a: int, h: Update) -> int:
    """Recovered arbitrary initialization, still evaluated via R and Pred."""
    return Pred(R(n, a, lifted_update(h)))


@cache
def parameter_update(p: int) -> Update:
    """A nonconstant parameterized update: 0 maps to p+1, positives to 0."""
    @cache
    def update(u: int) -> int:
        return C(u, p, 0)
    return update


def cache_sizes() -> dict[str, int]:
    """Diagnostic counts only; no arithmetic correctness assertion."""
    names = ("R", "S", "C", "Z", "even", "J", "K", "F", "H", "V", "Pred", "I")
    return {name: globals()[name].cache_info().currsize for name in names}
