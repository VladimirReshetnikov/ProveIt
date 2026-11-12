"""Finite diagnostics for the written successor-seeded scalar construction.

Every named map below follows its source term definition. R is memoized by
its fixed update function and seed; its only numerical equations are
R(0,a;h)=a+1 and R(n+1,a;h)=h(R(n,a;h)). T is the immediate two-case
constant-update consequence of these equations. No closed forms for N, M,
the scaling maps, the ramp, the factor map, or L are used to evaluate them.

The finite checks are diagnostics, not proofs of the arbitrary-element
identities or the interpretation theorem. Import this module to extend it
with the cycle-based predecessor construction.
"""
from __future__ import annotations

from functools import lru_cache
import json
from pathlib import Path


_orbits: dict[tuple[int, object], list[int]] = {}


def R(n: int, a: int, update) -> int:
    if type(n) is not int or type(a) is not int or n < 0 or a < 0:
        raise ValueError("R expects natural-number counter and seed")
    values = _orbits.setdefault((a, update), [a + 1])
    while len(values) <= n:
        value = update(values[-1])
        if type(value) is not int or value < 0:
            raise ValueError("The update left the natural-number domain")
        values.append(value)
    return values[n]


def T(n: int, a: int, b: int) -> int:
    return a + 1 if n == 0 else b


def Z(n: int) -> int:
    return T(n, 0, 0)


@lru_cache(None)
def N(n: int) -> int:
    return Z(R(n, 0, Z))


@lru_cache(None)
def j(u: int) -> int:
    return T(u, 0, T(Z(N(u)), 1, 0))


@lru_cache(None)
def M(n: int) -> int:
    return j(j(R(n, 0, j)))


def f2(u: int) -> int:
    return T(N(u), u + 1, 0)


@lru_cache(None)
def d2(n: int) -> int:
    return f2(R(n, 0, f2))


def f3(u: int) -> int:
    return T(M(u), u + 2, 0)


@lru_cache(None)
def d3(n: int) -> int:
    return f3(R(n, 0, f3))


def f(u: int) -> int:
    return T(M(u), u, T(Z(N(M(u))), u + 1, 0))


@lru_cache(None)
def G(n: int) -> int:
    return f(R(n, 1, f))


def Delta(e: int, a: int) -> int:
    return T(Z(e), a, a)


def F2(u: int) -> int:
    return d2(u) + 1


def F3(u: int) -> int:
    return d3(u) + 2


@lru_cache(None)
def H(u: int) -> int:
    return T(Z(N(u)), G(u), u)


def e_step(u: int) -> int:
    return d2(u) + 2


@lru_cache(None)
def E(x: int) -> int:
    return R(x, 0, e_step)


def Q(a: int) -> int:
    return d3(a) + 4


@lru_cache(None)
def L(x: int, y: int) -> int:
    return Z(N(R(y, E(x), H)))


def diagnostics(bound=48, comparison_bound=8):
    counts = {}

    def check(name, value):
        if not value:
            raise AssertionError(name)
        counts[name] = counts.get(name, 0) + 1

    for n in range(bound + 1):
        check("N Boolean and recurrence", N(n) in (0, 1) and N(n+1) == Z(N(n)))
        check("M range and recurrence", M(n) in (0, 1, 2) and M(n+1) == j(M(n)))
        check("M period", M(n+3) == M(n))
        check("d2 source recurrence", d2(n+1) == d2(n)+2)
        check("d3 source recurrence", d3(n+1) == d3(n)+3)
        check("d2,d3 standard diagnostics", d2(n) == 2*n and d3(n) == 3*n)
        check("parity scaling", N(d2(n)) == 0 and N(d3(n)) == N(n))
        check("ramp invariant", M(G(n)) == N(n))
        check("ramp two-step", G(n+2) == G(n)+3)
        check("ramp doubling", G(d2(n)) == d3(n))
        check("ramp tripling", G(d3(n)) == Delta(N(n), d3(G(n))))
        check("factor F2", H(F2(n)) == F3(n))
        check("factor F3", H(F3(n)) == F3(H(n)))
        check("factor parity", N(F3(n)) == N(n))
        check("seed Q", Q(n)+1 == F3(n+1))
    for x in range(comparison_bound + 1):
        check("seed E", E(x+1)+1 == F2(E(x)+1))
        for y in range(comparison_bound + 1):
            check("comparison zero row", L(0,y) == 1)
            check("comparison zero column", L(x+1,0) == 0)
            check("comparison diagonal recursion", L(x+1,y+1) == L(x,y))
            check("comparison persistence", L(x,y) != 1 or L(x,y+1) == 1)
            check("comparison standard diagnostic", L(x,y) == int(x <= y))
            check("seed rotation", R(y+1,E(x+1),H) == R(y,Q(E(x)),H))
    for a in range(7):
        for y in range(7):
            check("iterator factor", R(y,Q(a),H) == F3(R(y,a,H)))
    return {
        "status": "passed",
        "scope": "Finite source-macro diagnostics, not a proof assistant formalization",
        "bound": bound,
        "comparison_bound": comparison_bound,
        "checks": counts,
        "total_checks": sum(counts.values()),
        "finite_table_L": [[L(x,y) for y in range(comparison_bound+1)]
                           for x in range(comparison_bound+1)],
        "cached_orbits": len(_orbits),
        "cached_orbit_states": sum(map(len, _orbits.values())),
    }


if __name__ == "__main__":
    receipt = diagnostics()
    destination = Path(__file__).with_name("sr_comparator_diagnostics.json")
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k:v for k,v in receipt.items() if k != "finite_table_L"}, indent=2))
