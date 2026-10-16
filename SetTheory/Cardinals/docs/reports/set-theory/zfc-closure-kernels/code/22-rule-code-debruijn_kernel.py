"""A complete equality-free Hilbert kernel with freshness by construction.

This is an executable reference specification, not a compiled Turing machine.
It implements primitive falsity, implication, one binary relation and a unary
de Bruijn quantifier. One structural operation supplies both lifting for UD
and full variable instantiation for UI. There is no free-variable test,
fresh-name search, equality inference or unification in the kernel.

Nonlogical axioms, if supplied, must be closed. A theory emitter is an explicit
parameter; this file does not silently provide a PSC/EPSC emitter or a ZFC
calibration. The intended unbounded integer algorithm is distinguished from
Python's finite recursion/memory limits: an exception is never a refutation.
"""
from __future__ import annotations

from functools import lru_cache
from math import isqrt
from typing import Callable, Optional

# Zero is primitive Bottom. Positive codes use three residue classes, one for
# each positive constructor. Every natural is canonical; no truth/falsity
# alias or formula-normalization collapse is introduced.
BOT = 0


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    w = (isqrt(8 * n + 1) - 1) // 2
    b = n - w * (w + 1) // 2
    return w - b, b


def rel(i: int, j: int) -> int:
    return 3 * pair(i, j) + 1


def imp(a: int, b: int) -> int:
    return 3 * pair(a, b) + 2


def all_(a: int) -> int:
    return 3 * a + 3


def neg(a: int) -> int:
    return imp(a, BOT)


def ex(a: int) -> int:
    return neg(all_(neg(a)))


def normalize(a: int) -> int:
    # The three-positive-tag codec is a bijection; kept as an explicit
    # interface so callers cannot inherit the retired Top/Bottom alias rules.
    return a


def edit_index(i: int, depth: int, target: int) -> int:
    """target=0 inserts a free slot; target=j+1 deletes slot depth into j.

    A positive target already includes every binder traversed so far.
    """
    if i < depth:
        return i
    if target == 0:
        return i + 1
    if i == depth:
        return target - 1
    return i - 1


@lru_cache(None)
def edit(a: int, depth: int = 0, target: int = 0) -> int:
    """The only structural variable transformation used by the kernel."""
    if a == 0:
        return BOT
    q, tag = divmod(a - 1, 3)
    if tag == 0:
        i, j = unpair(q)
        return rel(edit_index(i, depth, target), edit_index(j, depth, target))
    if tag == 1:
        x, y = unpair(q)
        return imp(edit(x, depth, target), edit(y, depth, target))
    return all_(edit(q, depth + 1, target + 1 if target else 0))


def lift(a: int) -> int:
    return edit(a, 0, 0)


def subst0(a: int, j: int) -> int:
    return edit(a, 0, j + 1)


def K(a: int, b: int) -> int:
    return imp(a, imp(b, a))


def S(a: int, b: int, c: int) -> int:
    return imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))


def C(a: int, b: int) -> int:
    # Full classical contraposition; unlike Peirce alone this supplies the
    # required falsity/ex-falso behavior when Bottom is a primitive constant.
    return imp(imp(neg(a), neg(b)), imp(b, a))


def UI(a: int, j: int) -> int:
    return imp(all_(a), subst0(a, j))


def UD(a: int, b: int) -> int:
    return imp(all_(imp(lift(a), b)), imp(a, all_(b)))


# Every proof node is 8*payload+tag. Premise codes in GEN and MP are strictly
# below their containing node; formula payloads need no well-formedness test.
# 0 K, 1 S, 2 C, 3 UI, 4 UD, 5 GEN, 6 MP, 7 theory axiom.

def proof_k(a: int, b: int) -> int:
    return 8 * pair(a, b)


def proof_s(a: int, b: int, c: int) -> int:
    return 8 * pair(a, pair(b, c)) + 1


def proof_c(a: int, b: int) -> int:
    return 8 * pair(a, b) + 2


def proof_ui(a: int, j: int) -> int:
    return 8 * pair(a, j) + 3


def proof_ud(a: int, b: int) -> int:
    return 8 * pair(a, b) + 4


def proof_gen(p: int) -> int:
    return 8 * p + 5


def proof_mp(p: int, q: int) -> int:
    return 8 * pair(p, q) + 6


def proof_theory(i: int) -> int:
    return 8 * i + 7


def checker(theory: Callable[[int], Optional[int]] | None = None):
    """Return a total mathematical checker, with resource-bounded Python host.

    `theory(i)` must return None or a code for a closed axiom. Closedness is
    an emitter contract; it is not a hidden runtime free-variable check.
    """
    @lru_cache(None)
    def check(n: int) -> Optional[int]:
        payload, tag = divmod(n, 8)
        if tag in (0, 1, 2, 3, 4):
            x, y = unpair(payload)
            x = normalize(x)
            if tag == 0:
                return K(x, normalize(y))
            if tag == 1:
                y, z = unpair(y)
                return S(x, normalize(y), normalize(z))
            if tag == 2:
                return C(x, normalize(y))
            if tag == 3:
                return UI(x, y)
            return UD(x, normalize(y))
        if tag == 5:
            result = check(payload)
            return None if result is None else all_(result)
        if tag == 6:
            p, q = unpair(payload)
            antecedent, arrow = check(p), check(q)
            if antecedent is None or arrow is None or arrow % 3 != 2:
                return None
            a, b = unpair((arrow - 2) // 3)
            return b if a == antecedent else None
        result = None if theory is None else theory(payload)
        return None if result is None else normalize(result)
    return check


def refutation_search(theory: Callable[[int], Optional[int]]):
    """Unbounded exhaustive proof-tree enumeration, halting only at Bottom."""
    check = checker(theory)
    n = 0
    while True:
        if check(n) == BOT:
            return n
        n += 1


def decode(a: int):
    if a == 0:
        return ("bottom",)
    q, tag = divmod(a - 1, 3)
    if tag == 0:
        return ("rel", *unpair(q))
    if tag == 1:
        x, y = unpair(q)
        return ("imp", decode(x), decode(y))
    return ("all", decode(q))


def encode(a) -> int:
    if a[0] == "bottom":
        return BOT
    if a[0] == "rel":
        return rel(a[1], a[2])
    if a[0] == "imp":
        return imp(encode(a[1]), encode(a[2]))
    return all_(encode(a[1]))


def free_arity(a, depth=0) -> int:
    """Audit utility only: this routine is never called by the kernel."""
    if a[0] == "bottom":
        return 0
    if a[0] == "rel":
        return max(0, a[1] - depth + 1, a[2] - depth + 1)
    if a[0] == "imp":
        return max(free_arity(a[1], depth), free_arity(a[2], depth))
    return free_arity(a[1], depth + 1)


def satisfies(a, domain, relation, env) -> bool:
    """Independent ordinary, single-domain first-order semantics."""
    if a[0] == "bottom":
        return False
    if a[0] == "rel":
        return (env[a[1]], env[a[2]]) in relation
    if a[0] == "imp":
        return not satisfies(a[1], domain, relation, env) or satisfies(
            a[2], domain, relation, env
        )
    return all(satisfies(a[1], domain, relation, (x,) + env) for x in domain)
