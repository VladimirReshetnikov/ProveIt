"""Exact, bounded reference algorithms for Fermat's two-square theorem.

Only Python's standard library is used. Every mathematical search has a fixed
natural-number bound. The module is executable evidence, not a formal proof.
The report explains the natural-number encoding of the finite tables and Ints.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
import argparse
import json


def div0(a: int, b: int) -> int:
    """Totalized division; all natural-number arguments are nonnegative."""
    return a // b if b else 0


def mod0(a: int, b: int) -> int:
    return a % b if b else a


def prime_bit(n: int) -> bool:
    """The bounded primitive-recursive prime predicate used in the report."""
    answer = n >= 2
    for d in range(2, n):
        answer = answer and (n % d != 0)
    return answer


def isqrt_pr(n: int) -> int:
    """s(0)=0; s(k+1)=s(k)+[(s(k)+1)^2=k+1]."""
    s = 0
    for k in range(n):
        s += int((s + 1) ** 2 == k + 1)
    return s


def half_factorial_mod(p: int) -> int:
    """((p-1)//2)! modulo p, with natural truncated subtraction at p=0."""
    h = max(p - 1, 0) // 2
    value = mod0(1, p)
    for j in range(1, h + 1):
        value = mod0(value * j, p)
    return value


def grid_point(index: int, side: int) -> tuple[int, int]:
    return mod0(index, side), div0(index, side)


def grid_label(index: int, p: int, t: int, side: int) -> int:
    u, v = grid_point(index, side)
    return mod0(u + t * v, p)


def collision_table(p: int, t: int, side: int) -> tuple[int, int]:
    """First collision, ordered by later index and then earlier index.

    The p-entry table is a finite sequence, representable by a base-(p+2)
    natural number in iPRA. Zero means absent, i+1 stores the first index.
    All p+1 outer steps execute; after success the answer remains unchanged.
    A sentinel (0,p+1) totalizes the function, including the p=0 case.
    """
    if p == 0:
        return 0, 1
    seen = [0] * p
    answer = (0, p + 1)
    found = False
    for j in range(p + 1):
        r = grid_label(j, p, t, side)
        if not found:
            if seen[r] != 0:
                answer = (seen[r] - 1, j)
                found = True
            else:
                seen[r] = j + 1
    return answer


def collision_bounded(p: int, t: int, side: int) -> tuple[int, int]:
    """Table-free PR specification, at most p(p+1)/2 comparisons."""
    answer = (0, p + 1)
    found = False
    for j in range(p + 1):
        for i in range(j):
            if not found and grid_label(i, p, t, side) == grid_label(j, p, t, side):
                answer, found = (i, j), True
    return answer


@dataclass(frozen=True)
class GridCertificate:
    n: int
    t: int
    h: int
    i: int
    j: int
    x: int
    y: int
    a: int
    b: int
    square_case: bool = False


def grid_from_root(n: int, t: int) -> GridCertificate:
    """Total construction. Its correctness premise is n>0 and n|(t^2+1)."""
    h = isqrt_pr(n)
    if h * h == n:
        return GridCertificate(n, t, h, 0, 0, h, 0, 0, h, True)
    i, j = collision_table(n, t, h + 1)
    ui, vi = grid_point(i, h + 1)
    uj, vj = grid_point(j, h + 1)
    x, y = uj - ui, vj - vi
    a, b = sorted((abs(x), abs(y)))
    return GridCertificate(n, t, h, i, j, x, y, a, b)


def witness(p: int) -> tuple[int, int]:
    """Total PR witnesses A(p), B(p); specification is guarded by primality."""
    if p == 2:
        return 1, 1
    certificate = grid_from_root(p, half_factorial_mod(p))
    return certificate.a, certificate.b


def verify_grid(c: GridCertificate) -> bool:
    """Small independent certificate checker; does not run the search.

    Checking these identities proves the supplied individual representation.
    It does not establish the uniform iPRA theorem about every prime.
    """
    n, h = c.n, c.h
    if n < 1 or not (h >= 0 and h * h <= n < (h + 1) ** 2):
        return False
    if c.square_case:
        return (h * h == n and c.a == 0 and c.b == h
                and c.a * c.a + c.b * c.b == n)
    if (c.t * c.t + 1) % n != 0 or not (0 <= c.i < c.j <= n):
        return False
    ui, vi = c.i % (h + 1), c.i // (h + 1)
    uj, vj = c.j % (h + 1), c.j // (h + 1)
    if not all(0 <= value <= h for value in (ui, vi, uj, vj)):
        return False
    if (ui + c.t * vi) % n != (uj + c.t * vj) % n:
        return False
    if (c.x, c.y) != (uj - ui, vj - vi):
        return False
    norm = c.x * c.x + c.y * c.y
    return (0 < norm <= 2 * h * h < 2 * n and norm % n == 0
            and (c.a, c.b) == tuple(sorted((abs(c.x), abs(c.y))))
            and c.a * c.a + c.b * c.b == n)


@dataclass(frozen=True)
class DescentState:
    m: int
    a: int
    b: int


def centered(value: int, modulus: int) -> int:
    if modulus == 0:
        return value
    remainder = value % modulus
    return remainder if 2 * remainder <= modulus else remainder - modulus


def descent_step(state: DescentState) -> DescentState:
    """A total step; exactness of the quotients follows from the invariant."""
    m, a, b = state.m, state.a, state.b
    if m <= 1:
        return state
    r, s = centered(a, m), centered(b, m)
    return DescentState((r * r + s * s) // m,
                        (a * r + b * s) // m,
                        (b * r - a * s) // m)


def descent_trace(p: int, t: int) -> list[DescentState]:
    """Exactly p iterations, recording only state changes after the seed."""
    state = DescentState(div0(t * t + 1, p), t, 1)
    trace = [state]
    for _ in range(p):
        updated = descent_step(state)
        if updated != state:
            trace.append(updated)
        state = updated
    return trace


def verify_descent(p: int, trace: list[DescentState]) -> bool:
    if p <= 1 or not trace or len(trace) > p + 1:
        return False
    for state in trace:
        if not (1 <= state.m < p and state.a ** 2 + state.b ** 2 == p * state.m):
            return False
    for old, new in zip(trace, trace[1:]):
        r, s = centered(old.a, old.m), centered(old.b, old.m)
        if not (old.m > 1 and 0 < new.m < old.m and 2 * new.m <= old.m):
            return False
        if (r * r + s * s != old.m * new.m
                or old.a * r + old.b * s != old.m * new.a
                or old.b * r - old.a * s != old.m * new.b):
            return False
    return trace[-1].m == 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int)
    args = parser.parse_args()
    p = args.p
    if not prime_bit(p):
        raise SystemExit("p must be prime")
    if p == 2:
        print(json.dumps({"p": 2, "a": 1, "b": 1, "verified": True}, indent=2))
        return
    if p % 4 != 1:
        print(json.dumps({"p": p, "represented": False, "reason": "prime is 3 modulo 4"}, indent=2))
        return
    t = half_factorial_mod(p)
    certificate = grid_from_root(p, t)
    trace = descent_trace(p, t)
    assert verify_grid(certificate) and verify_descent(p, trace)
    print(json.dumps({"grid": asdict(certificate), "descent": [asdict(s) for s in trace],
                      "verified": True}, indent=2))


if __name__ == "__main__":
    main()
