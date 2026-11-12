"""Finite standard-model diagnostics, not a proof checker or metatheory.

F is the proposed source recursor. Other functions are the fixed source
macros in the report. D uses its proved two computation equations to
avoid repeatedly iterating a constant update. No numerical experiment
establishes a result about nonstandard elements.
"""
from functools import cache


def F(n, update):
    value = update(0) + 1
    for _ in range(n):
        value = update(value)
    return value


def eq(a, b):
    return int(a == b)


def D(n, a):
    return a + int(n == 0)


def band(a, b):
    return eq(D(a, eq(b, 0)), 0)


def bnot(a):
    return eq(a, 0)


def bor(a, b):
    return bnot(band(bnot(a), bnot(b)))


def mux(c, p, q):
    return bor(band(c, p), band(bnot(c), q))


@cache
def V(n, a):
    return F(n, lambda v: D(eq(v + 1, a), v))


@cache
def W(a):
    return V(a, a)


def predecessor_graph_value(a):
    if a < 2:
        return 0
    if a == 2:
        return 1
    return W(a)


@cache
def C(n, a):
    return F(n, lambda v: D(eq(v, a + 2), v))


def L(a, n):
    return eq(C(n, a), a + 2)


def Sel(bound, control, a, d):
    value = F(bound, lambda v: D(mux(control, eq(v, a + 2),
                                     eq(v, d + 2)), v))
    return W(W(value))


def clip_shifted(bound, value):
    """Requires bound,value >= 2; returns min(bound,value)."""
    return W(W(C(value, bound)))


def run_shifted(bound, encoded_counter, initial, update):
    """Two transient states: all real states are in [2,bound].

    This function is a metalevel expansion of a fixed finite update body.
    It does not add object-language quantification over functions.
    Sel's branch-local lemma permits unchosen values outside its bound.
    """
    def body(v):
        active = clip_shifted(bound, update(v))
        tail = Sel(bound + 2, eq(v, bound + 2), initial, active)
        middle = Sel(bound + 2, eq(v, bound + 1), bound + 2, tail)
        return Sel(bound + 2, eq(v, 0), bound, middle)
    return F(encoded_counter, body)

