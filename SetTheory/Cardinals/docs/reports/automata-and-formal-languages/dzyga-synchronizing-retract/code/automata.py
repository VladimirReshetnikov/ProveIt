"""Dzyga's binary automata and the cyclic-retract reset construction.

Only the Python standard library is required (Python >= 3.10).
Words act on the right: compose(f, g)[q] == g[f[q]].
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Sequence

Transformation = tuple[int, ...]

@dataclass(frozen=True)
class Automaton:
    a: Transformation
    b: Transformation

    def __post_init__(self) -> None:
        n = len(self.a)
        if n == 0 or len(self.b) != n:
            raise ValueError("Transition arrays must have equal positive length")
        if any(type(q) is not int or not 0 <= q < n for q in self.a + self.b):
            raise ValueError("Every transition target must be a state")

    @property
    def n(self) -> int:
        return len(self.a)


def make_family(k: int, *, shortened: bool = False) -> Automaton:
    """Make A_k, or its one-state-shorter nonsynchronizing comparison family.

    At the right endpoint the unused outward transition is a self-loop.
    At state zero b goes to 1. These conventions follow Figure 3 of the source.
    """
    if type(k) is not int or k < 1:
        raise ValueError("k must be an integer >= 1")
    m = 2 * k + 4
    n = 3 * k + 6 - int(shortened)
    a: list[int] = []
    b: list[int] = []
    for q in range(n):
        if q == 0:
            qa = 0
        elif q < m:
            qa = q + 1 if q % 2 else q - 1
        elif q == m:
            qa = m + 1
        elif q == m + 1:
            qa = 3
        elif q == n - 1 and q % 2 == 0:
            qa = q
        else:
            qa = q + 1 if q % 2 == 0 else q - 1
        if q < m:
            qb = q + 1 if q % 2 == 0 else q - 1
        elif q == m:
            qb = 2
        elif q == n - 1 and q % 2 == 1:
            qb = q
        else:
            qb = q + 1 if q % 2 else q - 1
        a.append(qa)
        b.append(qb)
    return Automaton(tuple(a), tuple(b))


def compose(f: Sequence[int], g: Sequence[int]) -> Transformation:
    """First apply f, then g (right-action convention)."""
    if len(f) != len(g):
        raise ValueError("Transformations have different degrees")
    return tuple(g[q] for q in f)


def power(f: Sequence[int], exponent: int) -> Transformation:
    if type(exponent) is not int or exponent < 0:
        raise ValueError("The exponent must be a nonnegative integer")
    answer = tuple(range(len(f)))
    base = tuple(f)
    while exponent:
        if exponent & 1:
            answer = compose(answer, base)
        base = compose(base, base)
        exponent >>= 1
    return answer


def word_action(aut: Automaton, word: Iterable[str]) -> Transformation:
    result = tuple(range(aut.n))
    for letter in word:
        if letter not in ("a", "b"):
            raise ValueError(f"Unknown letter {letter!r}")
        result = compose(result, aut.a if letter == "a" else aut.b)
    return result


def construction(k: int) -> dict[str, Transformation]:
    """Evaluate a straight-line description; never expand the long reset word."""
    aut = make_family(k)
    r = k + 4
    c = compose(aut.a, aut.b)
    p = power(c, r)
    f = compose(aut.a, p)
    g = compose(aut.b, p)
    back = power(c, r - 1)
    e = compose(compose(f, g), back)
    h = compose(e, back)
    reset = compose(compose(p, power(h, r - 2)), e)
    return {"c": c, "p": p, "F": f, "H": g, "back": back,
            "e": e, "h": h, "R": reset}


def reset_length(k: int) -> int:
    if type(k) is not int or k < 1:
        raise ValueError("k must be an integer >= 1")
    return 8 * k * k + 54 * k + 92


def expanded_reset_word(k: int, *, max_length: int = 1_000_000) -> str:
    """Expand only small cases; construction() handles large k without expansion."""
    length = reset_length(k)
    if length > max_length:
        raise ValueError(f"Word length {length} exceeds max_length={max_length}")
    r = k + 4
    p = "ab" * r
    back = "ab" * (r - 1)
    e = "a" + p + "b" + p + back
    return p + (e + back) * (r - 2) + e


def short_merging_word(k: int) -> str:
    make_family(k)
    return "ba" * (k + 2) + "ab" * (k + 2)


def quotient_colours(k: int, *, shortened: bool = False) -> Transformation:
    """Dihedral quotient for the shortened family; defective colouring for A_k."""
    aut = make_family(k, shortened=shortened)
    r, m = k + 4, 2 * k + 4
    colours = []
    for q in range(aut.n):
        if q == 0:
            colour = 0
        elif q <= m:
            colour = (q + 1) // 2 if q % 2 else r - q // 2
        else:
            t = q - m
            colour = r - 2 - (t - 1) // 2 if t % 2 else 2 + t // 2
        colours.append(colour % r)
    return tuple(colours)
