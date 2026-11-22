#!/usr/bin/env python3
"""Exact finite examples for the coupled approximate-action theorems.

This is a reference calculation, not an iPRA proof checker.  Every number in
the examples is a Fraction; no floating-point approximation is used.
"""

from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path


def dyadic(p: int) -> F:
    assert p >= 0
    return F(1, 2**p)


def add(x, y):
    return [a + b for a, b in zip(x, y)]


def scale(a, x):
    return [a * b for b in x]


def le(x, y):
    return len(x) == len(y) and all(a <= b for a, b in zip(x, y))


def mv(a, x):
    return [sum((v * z for v, z in zip(row, x)), F(0)) for row in a]


def norm(x, w):
    assert len(x) == len(w) > 0 and all(t > 0 for t in w)
    return max(abs(v) / t for v, t in zip(x, w))


def distance(x, y, w):
    return norm([a - b for a, b in zip(x, y)], w)


def ceil_rat(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def log_bound(x: F) -> int:
    """Least h in an explicit finite bound with x <= 2**h."""
    assert x >= 0
    for h in range(ceil_rat(x) + 2):
        if x <= 2**h:
            return h
    raise AssertionError("The elementary bound h+1 <= 2**h was violated")


def small_gain(a, w, s):
    assert s >= 1
    assert all(t > 0 for t in w)
    assert all(t >= 0 for row in a for t in row)
    return le(mv(a, w), scale(F(s - 1, s), w))


def automatic_weights(a, m: int, theta: F):
    """Construct SG1 from the supplied finite certificate A**m 1 <= theta 1."""
    assert m >= 1 and 0 <= theta < 1
    v = [F(1)] * len(a)
    w = [F(0)] * len(a)
    for _ in range(m):
        w = add(w, v)
        v = mv(a, v)
    assert le(v, [theta] * len(a))
    s = max(1, ceil_rat(max(w) / (1 - theta)))
    assert small_gain(a, w, s)
    return w, s


def supersolution(a, w, s, residual, n):
    """Finite Neumann prefix plus the certified geometric remainder SG18."""
    assert n >= 0 and all(r >= 0 for r in residual)
    assert small_gain(a, w, s)
    u = [F(0)] * len(a)
    v = list(residual)
    for _ in range(n):
        u = add(u, v)
        v = mv(a, v)
    z = add(u, scale(s * norm(v, w), w))
    assert le(add(mv(a, z), residual), z)
    return z


A = [[F(0), F(2)], [F(1, 8), F(0)]]
W = [F(4), F(1)]
S = 2
BOX = [(F(0), F(4)), (F(0), F(1))]
DIAMETER = F(1)
FIXED = [F(2), F(1, 2)]


def exact_action(x):
    return [1 + 2 * x[1], x[0] / 8 + F(1, 4)]


def action(x, p):
    """Round downward to a weight-scaled dyadic grid; this preserves BOX."""
    y = exact_action(x)
    out = []
    for yi, wi in zip(y, W):
        mesh = wi * dyadic(p)
        q = yi / mesh
        out.append((q.numerator // q.denominator) * mesh)
    assert in_box(out)
    return out


def in_box(x):
    return all(lo <= t <= hi for t, (lo, hi) in zip(x, BOX))


def orbit(p, n):
    x = [F(0), F(0)]
    for _ in range(n):
        x = action(x, p)
    return x


def producer(k):
    h = log_bound(S * DIAMETER)
    g = log_bound(F(S * (2 * S + 1)))
    p = k + g + 1
    n = S * (k + h + 1)
    x = orbit(p, n)
    residual = distance(x, action(x, p), W) + dyadic(p)
    assert S * residual <= dyadic(k)
    return x, p, n, residual


def delayed_run(p, steps, delay):
    """Cyclic single-coordinate updates, all reads delayed by at most delay."""
    history = [[F(0), F(0)]]
    for t in range(steps):
        i = t % len(W)
        stale = history[max(0, t - delay)]
        new = list(history[-1])
        new[i] = action(stale, p)[i]
        assert in_box(new)
        history.append(new)
    return history[-1]


def asynchronous_producer(k, delay):
    window = len(W)
    block = window + delay
    h = log_bound(DIAMETER)
    g = log_bound(F(S))
    p = k + g + 2
    steps = block * S * (k + h + 2)
    y = delayed_run(p, steps, delay)
    for j in range(9):
        q, *_ = producer(j)
        assert distance(y, q, W) <= dyadic(k) / 2 + dyadic(j)
    return y, p, steps


def rational_json(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, (tuple, list)):
        return [rational_json(y) for y in x]
    if isinstance(x, dict):
        return {k: rational_json(v) for k, v in x.items()}
    return x


def verify():
    assert small_gain(A, W, S)
    assert exact_action(FIXED) == FIXED
    auto_w, auto_s = automatic_weights(A, 2, F(1, 4))
    assert auto_w == [F(3), F(9, 8)] and auto_s == 4

    points = [[F(i, 2), F(j, 8)] for i in range(9) for j in range(9)]
    action_checks = 0
    for x in points:
        for y in points[::8]:
            for p, q in [(0, 0), (1, 3), (3, 2), (5, 6)]:
                lhs = [abs(a - b) for a, b in zip(action(x, p), action(y, q))]
                rhs = add(mv(A, [abs(a - b) for a, b in zip(x, y)]),
                          scale(dyadic(p) + dyadic(q), W))
                assert le(lhs, rhs)
                action_checks += 1

    names = [producer(k) for k in range(13)]
    for k, (x, *_rest) in enumerate(names):
        for l, (y, *_more) in enumerate(names):
            assert distance(x, y, W) <= dyadic(k) + dyadic(l)

    candidate = [F(199, 100), F(501, 1000)]
    r = [abs(x - y) for x, y in zip(candidate, exact_action(candidate))]
    assert r == [F(3, 250), F(9, 4000)]
    zs = [supersolution(A, W, S, r, n) for n in range(9)]
    assert zs[0] == [F(3, 125), F(3, 500)]
    assert zs[2] == [F(9, 400), F(21, 4000)]
    sharp = [F(11, 500), F(1, 200)]
    assert add(mv(A, sharp), r) == sharp
    for z in zs:
        assert le([abs(a - b) for a, b in zip(candidate, FIXED)], z)

    rp = add([abs(x - y) for x, y in zip(candidate, action(candidate, 20))],
             scale(dyadic(20), W))
    zp = supersolution(A, W, S, rp, 8)
    for k, (q, *_rest) in enumerate(names):
        assert le([abs(x - y) for x, y in zip(candidate, q)],
                  add(zp, scale(dyadic(k), W)))

    async_examples = []
    for delay in range(5):
        ys = [asynchronous_producer(k, delay) for k in range(9)]
        for k, (y, *_rest) in enumerate(ys):
            for l, (z, *_more) in enumerate(ys):
                assert distance(y, z, W) <= dyadic(k) + dyadic(l)
        async_examples.append({"delay": delay, "outputs": ys})

    # A failed finite certificate is rejected; no search for an undisclosed
    # spectral gap or update bound is attempted.
    assert not small_gain(A, [F(1), F(1)], S)
    assert not small_gain([[F(1)]], [F(1)], 10)

    return rational_json({
        "status": "all exact finite checks passed",
        "logical_status": "reference computation, not an iPRA proof checker",
        "action_contract_instances": action_checks,
        "matrix": A, "weights": W, "s": S,
        "automatic_weights": auto_w, "automatic_s": auto_s,
        "regular_name_outputs": names,
        "residual_candidate": candidate, "residual": r,
        "neumann_supersolutions": zs,
        "exact_linear_supersolution": sharp,
        "rounded_action_supersolution": zp,
        "asynchronous_examples": async_examples,
    })


if __name__ == "__main__":
    result = verify()
    out = Path(__file__).with_name("small_gain_checks.json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    print(f"Verified {result['action_contract_instances']} action instances.")
    print(f"Exact record: {out}")
