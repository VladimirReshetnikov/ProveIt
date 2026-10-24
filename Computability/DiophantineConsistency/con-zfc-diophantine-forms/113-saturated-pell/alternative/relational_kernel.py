#!/usr/bin/env python3
"""Exact local equational-proof kernel; NOT a Con(ZFC) polynomial.

All arithmetic is over nonnegative integers.  Every natural number is the
code of a unique term built from eps, id, neg, conv, join, and comp.

The seven-variable polynomial kernel has degree 14 and 41 live binary
arithmetic operations in the supplied straight-line evaluator.  It checks
one inference from two equations; chronology and axiom admission are
separate and are checked by check_proof.

No finite NBG axiom tuple and no Diophantine history compiler are supplied.
"""

from dataclasses import dataclass
from functools import lru_cache
from math import isqrt
import json
import random


def require_natural(*xs):
    if any(type(x) is not int or x < 0 for x in xs):
        raise ValueError("natural-number inputs required")


def pair(x, y):
    require_natural(x, y)
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n):
    require_natural(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    y = n - s * (s + 1) // 2
    return s - y, y


def neg(a):
    return 4 * a + 2


def conv(a):
    return 4 * a + 3


def join(a, z):
    return 2 * (a + z) * (a + z + 1) + 4 * z + 4


def comp(a, z):
    return join(a, z) + 1


@lru_cache(maxsize=None)
def decode(n):
    require_natural(n)
    if n == 0:
        return ("eps",)
    if n == 1:
        return ("id",)
    q, r = divmod(n, 4)
    if r in (2, 3):
        return ("neg" if r == 2 else "conv", decode(q))
    a, b = unpair(q - 1)
    return ("join" if r == 0 else "comp", decode(a), decode(b))


def encode(term):
    tag = term[0]
    if tag == "eps":
        return 0
    if tag == "id":
        return 1
    if tag == "neg":
        return neg(encode(term[1]))
    if tag == "conv":
        return conv(encode(term[1]))
    if tag == "join":
        return join(encode(term[1]), encode(term[2]))
    if tag == "comp":
        return comp(encode(term[1]), encode(term[2]))
    raise ValueError("unknown term constructor")


def kernel(u, v, a, b, c, d, z):
    """K=0 iff common-left transitivity or one of four congruence rules."""
    kt = (a - c) ** 2 + (u - b) ** 2 + (v - d) ** 2
    q = u - 4 * a - 2
    ku = (q * (q - 1)) ** 2 + (v - u - 4 * (b - a)) ** 2
    r = u - join(a, z)
    kb = (r * (r - 1)) ** 2 + (
        v - u - 2 * (b - a) * (a + b + 2 * z + 1)
    ) ** 2
    return kt * ku * kb


def semantic_step(u, v, a, b, c, d, z):
    return (
        (a == c and u == b and v == d)
        or (u == neg(a) and v == neg(b))
        or (u == conv(a) and v == conv(b))
        or (u == join(a, z) and v == join(b, z))
        or (u == comp(a, z) and v == comp(b, z))
    )


def circuit():
    """41 live binary +,-,* gates; each squaring is one multiplication."""
    rows = []
    def op(kind, x, y):
        out = "g" + str(len(rows))
        rows.append((out, kind, x, y))
        return out
    sub = lambda x, y: op("-", x, y)
    add = lambda x, y: op("+", x, y)
    mul = lambda x, y: op("*", x, y)
    sq = lambda x: mul(x, x)
    kt = add(add(sq(sub("a", "c")), sq(sub("u", "b"))), sq(sub("v", "d")))
    delta = sub("b", "a")
    outdiff = sub("v", "u")
    q = sub(sub("u", mul(4, "a")), 2)
    ku = add(sq(mul(q, sub(q, 1))), sq(sub(outdiff, mul(4, delta))))
    az = add("a", "z")
    twoz = mul(2, "z")
    base = mul(2, add(add(mul(az, add(az, 1)), twoz), 2))
    r = sub("u", base)
    slope = add(add(add("a", "b"), twoz), 1)
    kb = add(sq(mul(r, sub(r, 1))), sq(sub(outdiff, mul(mul(2, delta), slope))))
    output = mul(mul(kt, ku), kb)
    return rows, output


def evaluate_circuit(values):
    rows, output = circuit()
    env = dict(values)
    for dst, op, x, y in rows:
        x = env[x] if isinstance(x, str) else x
        y = env[y] if isinstance(y, str) else y
        env[dst] = x + y if op == "+" else x - y if op == "-" else x * y
    return env[output]


def instantiate(template, env):
    """A finite schema template, with variables ('var',i), yields a term code."""
    tag = template[0]
    if tag == "var":
        return env[template[1]]
    if tag == "eps":
        return 0
    if tag == "id":
        return 1
    if tag in ("neg", "conv"):
        x = instantiate(template[1], env)
        return neg(x) if tag == "neg" else conv(x)
    x = instantiate(template[1], env)
    y = instantiate(template[2], env)
    if tag == "join":
        return join(x, y)
    if tag == "comp":
        return comp(x, y)
    raise ValueError("unknown schema constructor")


@dataclass(frozen=True)
class Line:
    equation: tuple[int, int]
    parents: tuple[int, int] | None = None
    z: int = 0
    schema: int | None = None
    env: tuple[int, ...] = ()


def check_proof(lines, schemas, target):
    """A total finite-list checker for the supplied explicit schema theory.

    This function does not hide an axiomhood oracle: schemas are finite
    pairs of constructor templates.  A line is either an exact schema
    instance or a kernel inference from strictly earlier lines.
    """
    if not lines:
        return False
    try:
        for i, line in enumerate(lines):
            u, v = line.equation
            require_natural(u, v, line.z, *line.env)
            if line.schema is not None:
                if line.parents is not None or not (0 <= line.schema < len(schemas)):
                    return False
                lhs, rhs = schemas[line.schema]
                if (instantiate(lhs, line.env), instantiate(rhs, line.env)) != (u, v):
                    return False
            else:
                if line.parents is None or len(line.parents) != 2:
                    return False
                j, k = line.parents
                if not (type(j) is int and type(k) is int and 0 <= j < i and 0 <= k < i):
                    return False
                a, b = lines[j].equation
                c, d = lines[k].equation
                if kernel(u, v, a, b, c, d, line.z) != 0:
                    return False
        return lines[-1].equation == target
    except (ValueError, IndexError, KeyError, TypeError):
        return False


def self_test():
    for n in range(10000):
        assert encode(decode(n)) == n
        a, b = unpair(n)
        assert pair(a, b) == n
    for a in range(32):
        for b in range(32):
            assert unpair(pair(a, b)) == (a, b)
            for constructor, tag in ((join, "join"), (comp, "comp")):
                assert decode(constructor(a, b)) == (tag, decode(a), decode(b))
    rng = random.Random(20261024)
    for _ in range(20000):
        xs = tuple(rng.randrange(64) for _ in range(7))
        assert (kernel(*xs) == 0) == semantic_step(*xs)
        assert evaluate_circuit(dict(zip(("u", "v", "a", "b", "c", "d", "z"), xs))) == kernel(*xs)
    positive_cases = 0
    for a in range(12):
        for b in range(12):
            for z in range(12):
                c, d = a, z
                outputs = [(b, d), (neg(a), neg(b)), (conv(a), conv(b)),
                           (join(a, z), join(b, z)), (comp(a, z), comp(b, z))]
                for u, v in outputs:
                    assert kernel(u, v, a, b, c, d, z) == 0
                    assert semantic_step(u, v, a, b, c, d, z)
                    positive_cases += 1
    schemas = [(("eps",), ("id",)), (("var", 0), ("var", 0))]
    proof = [Line((0, 1), schema=0),
             Line((2, 6), parents=(0, 0)),
             Line((3, 7), parents=(0, 0)),
             Line((join(0, 2), join(1, 2)), parents=(0, 0), z=2),
             Line((comp(0, 2), comp(1, 2)), parents=(0, 0), z=2),
             Line((0, 0), schema=1, env=(0,)),
             Line((1, 0), parents=(0, 5))]
    assert check_proof(proof, schemas, (1, 0))
    assert not check_proof([Line((0, 1), parents=(0, 0))], schemas, (0, 1))
    assert not check_proof([Line((0, 2), schema=0)], schemas, (0, 2))
    assert not check_proof(proof, schemas, (0, 1))
    rows, output = circuit()
    assert len(rows) == 41
    return {"code_roundtrips": 10000, "pair_roundtrips": 10000,
            "constructor_tuple_checks": 2048, "random_polynomial_checks": 20000,
            "positive_rule_cases": positive_cases,
            "circuit_binary_operations": len(rows), "exact_degree": 14,
            "status": "local kernel only; no Con(ZFC) calibration or history compiler"}


if __name__ == "__main__":
    print(json.dumps(self_test(), indent=2))
