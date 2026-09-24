#!/usr/bin/env python3
"""Exact arithmetic checks accompanying quaternionic_analysis.tex.

Requires Python 3.9+; uses only the standard library. These are finite
algebraic and polynomial-differential checks, not a formal verification
of the analytic theorems. All comparisons use rational arithmetic.
"""
from fractions import Fraction as F
from random import Random
from typing import Dict, List, Tuple

Q = Tuple[F, F, F, F]
Exp = Tuple[int, int, int, int]
MV = Dict[Exp, Q]


def quat(a=0, b=0, c=0, d=0) -> Q:
    return F(a), F(b), F(c), F(d)


ZERO, ONE = quat(), quat(1)
I, J, K = quat(0, 1), quat(0, 0, 1), quat(0, 0, 0, 1)
BASIS = (ONE, I, J, K)


def add(a: Q, b: Q) -> Q:
    return tuple(x + y for x, y in zip(a, b))


def scale(a: Q, r: F) -> Q:
    return tuple(r * x for x in a)


def sub(a: Q, b: Q) -> Q:
    return add(a, scale(b, -1))


def mul(p: Q, q: Q) -> Q:
    a, b, c, d = p
    e, f, g, h = q
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def conj(q: Q) -> Q:
    return q[0], -q[1], -q[2], -q[3]


def norm2(q: Q) -> F:
    return sum(x*x for x in q)


def inv(q: Q) -> Q:
    n = norm2(q)
    if not n:
        raise ZeroDivisionError("Cannot invert the zero quaternion")
    return scale(conj(q), 1/n)


# One central variable, with quaternionic coefficients on the right.
def star(p: List[Q], q: List[Q]) -> List[Q]:
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] = add(out[i+j], mul(a, b))
    return out


def evaluate(p: List[Q], q: Q) -> Q:
    out = ZERO
    for a in reversed(p):
        out = add(mul(q, out), a)
    return out


def pconj(p: List[Q]) -> List[Q]:
    return [conj(a) for a in p]


def symm(p: List[Q]) -> List[Q]:
    return star(p, pconj(p))


# Four commuting real coordinates with quaternionic values.
def mv_add(p: MV, q: MV) -> MV:
    out = dict(p)
    for e, a in q.items():
        out[e] = add(out.get(e, ZERO), a)
    return {e: a for e, a in out.items() if a != ZERO}


def mv_mul(p: MV, q: MV) -> MV:
    out: MV = {}
    for e, a in p.items():
        for h, b in q.items():
            k = tuple(x+y for x, y in zip(e, h))
            out[k] = add(out.get(k, ZERO), mul(a, b))
    return {e: a for e, a in out.items() if a != ZERO}


def partial(p: MV, axis: int) -> MV:
    out: MV = {}
    for e, a in p.items():
        if e[axis]:
            k = list(e)
            k[axis] -= 1
            out[tuple(k)] = scale(a, e[axis])
    return out


def laplacian(p: MV) -> MV:
    out: MV = {}
    for axis in range(4):
        out = mv_add(out, partial(partial(p, axis), axis))
    return out


def fueter(p: MV) -> MV:
    out: MV = {}
    for axis, unit in enumerate(BASIS):
        out = mv_add(out, {e: mul(unit, a)
                          for e, a in partial(p, axis).items()})
    return out


def main() -> None:
    rng = Random(20260920)
    count = 0

    def check(condition: bool, label: str) -> None:
        nonlocal count
        if not condition:
            raise AssertionError(label)
        count += 1

    def random_q() -> Q:
        return quat(*(rng.randint(-3, 3) for _ in range(4)))

    for case in range(60):
        p = [random_q() for _ in range(4)]
        g = [random_q() for _ in range(3)]
        q, s = random_q(), random_q()
        u = evaluate(p, q)
        expected = ZERO if u == ZERO else mul(
            u, evaluate(g, mul(mul(inv(u), q), u)))
        check(evaluate(star(p, g), q) == expected,
              f"star evaluation, case {case}")
        check(all(a[1:] == (0, 0, 0) for a in symm(p)),
              "symmetrization has real coefficients")
        check(symm(star(p, g)) == star(symm(p), symm(g)),
              "multiplicativity of symmetrization")
        check(norm2(sub(ONE, mul(q, conj(s)))) - norm2(sub(q, s))
              == (1-norm2(q))*(1-norm2(s)), "ball norm identity")

        n = evaluate(symm(p), q)
        if n != ZERO:
            c = evaluate(pconj(p), q)
            check(c != ZERO, "nonzero conjugate value")
            t = mul(mul(inv(c), q), c)
            value = evaluate(p, t)
            reciprocal = mul(inv(n), c)
            check(reciprocal == inv(value), "reciprocal evaluation")
            check(mul(mul(inv(value), t), value) == q, "inverse T map")
            lhs = mul(inv(n), evaluate(star(pconj(p), g), q))
            check(lhs == mul(inv(value), evaluate(g, t)),
                  "regular quotient evaluation")

        delta = add(sub(mul(q, q), scale(q, 2*s[0])), quat(norm2(s)))
        if delta != ZERO:
            kernel = scale(mul(inv(delta), sub(q, conj(s))), -1)
            check(sub(mul(kernel, s), mul(q, kernel)) == ONE,
                  "Cauchy kernel resolvent identity")

    p = star([scale(I, -1), ONE], [scale(J, -1), ONE])
    check(p == [K, scale(add(I, J), -1), ONE], "noncommutative factors")
    check(evaluate(p, I) == ZERO, "first factor gives a zero")
    check(evaluate(p, J) == scale(K, 2), "second factor is not a zero")
    check(symm(p) == [ONE, ZERO, quat(2), ZERO, ONE], "spherical norm")
    check(evaluate(symm([scale(I, -1), ONE]), J) == ZERO,
          "symmetrization can vanish away from the pointwise zero")
    check(norm2(sub(J, I)) == 2, "pointwise norm is different")

    # Symbolic polynomial identities: no sampled real coordinates are used.
    x = {(1, 0, 0, 0): ONE, (0, 1, 0, 0): I,
         (0, 0, 1, 0): J, (0, 0, 0, 1): K}
    power: MV = {(0, 0, 0, 0): ONE}
    for degree in range(9):
        lp = laplacian(power)
        check(fueter(lp) == {}, f"D Delta q^{degree} = 0")
        check(laplacian(lp) == {}, f"Delta^2 q^{degree} = 0")
        if degree == 1:
            check(fueter(power) == {(0, 0, 0, 0): quat(-2)}, "D q = -2")
        if degree == 2:
            check(lp == {(0, 0, 0, 0): quat(-4)}, "Delta q^2 = -4")
        if degree == 3:
            target = {(1, 0, 0, 0): quat(-12),
                      (0, 1, 0, 0): scale(I, -4),
                      (0, 0, 1, 0): scale(J, -4),
                      (0, 0, 0, 1): scale(K, -4)}
            check(lp == target, "Delta q^3 = -4(3 x0 + Im q)")
        power = mv_mul(power, x)

    plane = {(0, 1, 0, 0): ONE, (1, 0, 0, 0): scale(I, -1)}
    check(fueter(plane) == {}, "plane-zero Fueter counterexample")
    print(f"PASS: {count} exact checks.")
    print("60 deterministic rational-quaternion test cases for the regular")
    print("product, scalar norm, reciprocal, T map, quotient and Cauchy kernel.")
    print("Symbolic polynomial checks of D Delta q^n and Delta^2 q^n, 0 <= n <= 8.")
    print("No floating-point arithmetic; standard library only.")
    print("These checks supplement, but do not formally verify, the paper's proofs.")


if __name__ == "__main__":
    main()
