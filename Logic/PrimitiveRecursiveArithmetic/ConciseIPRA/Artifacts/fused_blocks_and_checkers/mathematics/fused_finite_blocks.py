#!/usr/bin/env python3
"""Untrusted raw-tree compiler and exact-accounting checks for finite blocks.

No proof checker is imported. All arithmetic definitions are expanded into
zero, successor, variables and the scalar iterator. No DAG sharing is counted.
The mathematical soundness proof is in fused_finite_blocks_note.md.
"""

from functools import lru_cache
from itertools import product
import json
from pathlib import Path


_serial = 0


def fresh():
    global _serial
    _serial += 1
    return "_b" + str(_serial)


def V(name):
    return ("v", name)


Z = ("0",)


def S(t):
    return ("S", t)


ONE = S(Z)
TWO = S(ONE)


def I(n, a, body):
    u = fresh()
    return ("I", n, a, u, body(V(u)))


def C(n, a, b):
    return I(n, a, lambda u: b)


def eq(s, t):
    return ("=", s, t)


def D(x, y, a):
    return ("D", x, y, a)


@lru_cache(None)
def fv(a):
    tag = a[0]
    if tag == "v":
        return frozenset((a[1],))
    if tag == "0":
        return frozenset()
    if tag == "S":
        return fv(a[1])
    if tag == "I":
        return fv(a[1]) | fv(a[2]) | (fv(a[4]) - {a[3]})
    if tag == "=":
        return fv(a[1]) | fv(a[2])
    if tag == "D":
        return fv(a[3]) - {a[1], a[2]}
    raise ValueError("unknown syntax")


def subst(a, x, value):
    """Capture-avoiding substitution, with generated names globally fresh.

    Public example-variable names never start with '_b'; those names are
    reserved for this compiler's generated binding names.
    """
    tag = a[0]
    if x not in fv(a):
        return a
    if tag == "v":
        return value if a[1] == x else a
    if tag == "0":
        return a
    if tag == "S":
        return S(subst(a[1], x, value))
    if tag == "I":
        _, n, seed, u, h = a
        if u != x and u in fv(value) and x in fv(h):
            new = fresh()
            h = subst(h, u, V(new))
            u = new
        return ("I", subst(n, x, value), subst(seed, x, value), u,
                h if u == x else subst(h, x, value))
    if tag == "=":
        return eq(subst(a[1], x, value), subst(a[2], x, value))
    if tag == "D":
        _, u, v, h = a
        if x in (u, v):
            return a
        if u in fv(value):
            new = fresh()
            h = subst(h, u, V(new))
            u = new
        if v in fv(value):
            new = fresh()
            h = subst(h, v, V(new))
            v = new
        return D(u, v, subst(h, x, value))
    raise ValueError("unknown syntax")


def gate(control, a):
    if a[0] == "=":
        return eq(C(control, Z, a[1]), C(control, Z, a[2]))
    if fv(control) & {a[1], a[2]}:
        raise ValueError("gate control captured")
    return D(a[1], a[2], gate(control, a[3]))


def align(a, x, y):
    return subst(subst(a[3], a[1], V(x)), a[2], V(y))


def mix(control, a, b):
    if a[0] == b[0] == "=":
        return eq(C(control, a[1], b[1]), C(control, a[2], b[2]))
    x, y = fresh(), fresh()
    aa = align(a, x, y) if a[0] == "D" else gate(V(y), a)
    bb = align(b, x, y) if b[0] == "D" else gate(V(y), b)
    return D(x, y, mix(control, aa, bb))


def let(w, seed, a):
    if a[0] == "=":
        return eq(("I", ONE, seed, w, a[1]),
                  ("I", ONE, seed, w, a[2]))
    if w in (a[1], a[2]) or fv(seed) & {a[1], a[2]}:
        raise ValueError("let capture")
    return D(a[1], a[2], let(w, seed, a[3]))


def parity(v):
    return I(v, Z, lambda u: C(u, ONE, Z))


def ceil_ramp(v):
    def cycle(a):
        return I(a, TWO, lambda w: C(w, ONE, Z))
    def mod3(a):
        return I(a, Z, cycle)
    return I(v, Z, lambda u: S(C(mod3(u), S(u), u)))


def floor_cycle(v):
    return I(S(v), v, lambda w: C(w, S(v), Z))


def floor_mod3(v):
    return I(v, Z, floor_cycle)


def floor_ramp(v):
    return I(v, Z, lambda u: S(C(floor_mod3(u), u, S(u))))


def transition(v):
    return I(v, v, lambda u: C(u, floor_ramp(v), Z))


def selector(v, operands, fused=True, use_floor=False):
    if len(operands) == 1:
        return operands[0]
    w = fresh()
    tail = selector(V(w), operands[1:], fused, use_floor)
    if fused:
        return let(w, transition(v), mix(V(w), operands[0], tail))
    ramp = floor_ramp if use_floor else ceil_ramp
    return mix(parity(v), let(w, ramp(v), tail), operands[0])


def block(operands, existential=False, fused=True, use_floor=False):
    if not operands:
        raise ValueError("nonempty finite block required")
    ordered = sorted(operands, key=rank, reverse=True)
    x, y = fresh(), fresh()
    body = selector(V(x) if existential else V(y), ordered, fused, use_floor)
    return D(x, y, gate(V(y), body))


def size(a):
    tag = a[0]
    if tag in ("v", "0"):
        return 1
    if tag == "S":
        return 1 + size(a[1])
    if tag == "I":
        return 1 + size(a[1]) + size(a[2]) + size(a[4])
    if tag == "=":
        return 1 + size(a[1]) + size(a[2])
    if tag == "D":
        return 1 + size(a[3])
    raise ValueError("unknown syntax")


def rank(a):
    return 0 if a[0] == "=" else 1 + rank(a[3])


def payload(a):
    return size(a) - rank(a) - 1


def evaluate(a, env):
    return _evaluate(a, tuple(sorted((x, env[x]) for x in fv(a))))


@lru_cache(None)
def _evaluate(a, entries):
    env = dict(entries)
    tag = a[0]
    if tag == "v":
        return env[a[1]]
    if tag == "0":
        return 0
    if tag == "S":
        return 1 + evaluate(a[1], env)
    if tag == "I":
        _, count, seed, u, body = a
        n = evaluate(count, env)
        value = evaluate(seed, env)
        if n and u not in fv(body):
            return evaluate(body, env)
        for _ in range(n):
            env[u] = value
            value = evaluate(body, env)
        return value
    raise ValueError("term expected")


def bounded_truth(a, env, domain=(0, 1, 2)):
    """Finite-domain smoke check only, NOT the intended quantifier semantics."""
    if a[0] == "=":
        return evaluate(a[1], env) == evaluate(a[2], env)
    _, x, y, body = a
    for witness in domain:
        local = dict(env, **{x: witness, y: 0})
        if not bounded_truth(body, local, domain):
            return True
        if all(bounded_truth(body, dict(local, **{y: z}), domain)
               for z in domain):
            return True
    return False


def example(j, depth):
    a = eq(V("a" + str(j)), Z)
    for _ in range(depth):
        x, y = fresh(), fresh()
        # The bound variable matters, so this is not merely vacuous wrapping.
        a = D(x, y, gate(V(y), a))
    return a


def minimum_padding(ranks):
    @lru_cache(None)
    def top(mask):
        return max(ranks[j] for j in range(len(ranks)) if mask >> j & 1)
    @lru_cache(None)
    def solve(mask):
        if mask & (mask - 1) == 0:
            return 0
        first = mask & -mask
        values = []
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if right and left & first:
                values.append(solve(left) + solve(right)
                              + abs(top(left) - top(right)))
            left = (left - 1) & mask
        return min(values)
    return solve((1 << len(ranks)) - 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    x = V("x")
    pieces = {"parity": parity(x), "ceiling_ramp": ceil_ramp(x),
              "floor_cycle": floor_cycle(x), "floor_mod3": floor_mod3(x),
              "floor_ramp": floor_ramp(x), "transition": transition(x)}
    sizes = {name: size(t) for name, t in pieces.items()}
    require(sizes == {"parity": 8, "ceiling_ramp": 21, "floor_cycle": 9,
                      "floor_mod3": 12, "floor_ramp": 20, "transition": 26},
            "expanded arithmetic sizes")
    arithmetic_checks = 0
    for n in range(129):
        env = {"x": n}
        require(evaluate(pieces["floor_ramp"], env) == 3 * n // 2,
                ("floor ramp", n))
        require(evaluate(pieces["transition"], env) == (0 if n % 2 else 3 * n // 2),
                ("transition", n))
        arithmetic_checks += 2
    count_checks, rows = 0, []
    for n in (1, 2, 3, 4, 8, 16, 32, 64):
        for shift in range(5):
            operands = [example(j, (3 * j + shift) % 6) for j in range(n)]
            high, low = max(map(rank, operands)), min(map(rank, operands))
            old_expected = sum(map(payload, operands)) + 66 * (n - 1) + 6 * (high - low) + high + 8
            new_expected = old_expected - 4 * (n - 1)
            for existential in (False, True):
                new = block(operands, existential, True)
                old = block(operands, existential, False)
                middle = block(operands, existential, False, True)
                require(rank(new) == rank(old) == rank(middle) == high + 1, "block rank")
                require(size(old) == old_expected, "old block size")
                require(size(middle) == old_expected - 2 * (n - 1), "floor control size")
                require(size(new) == new_expected, "new block size")
                require(fv(new) == fv(old) == fv(middle) == frozenset("a" + str(j) for j in range(n)),
                        "block free variables")
                count_checks += 1
        flat = [eq(V("a" + str(j)), Z) for j in range(n)]
        rows.append({"operand_count": n, "old_nodes": size(block(flat, fused=False)),
                     "separate_floor_nodes": size(block(flat, fused=False, use_floor=True)),
                     "new_nodes": size(block(flat)), "saving": 4 * (n - 1)})
    padding_checks = 0
    for n in range(1, 6):
        for ranks in product(range(4), repeat=n):
            require(minimum_padding(ranks) == max(ranks) - min(ranks),
                    ("minimum padding", ranks))
            padding_checks += 1
    route_checks, routes = 0, []
    for n in range(1, 6):
        operands = [eq(V("a" + str(j)), Z) for j in range(n)]
        a = selector(x, operands)
        env = {"a" + str(j): j + 10 for j in range(n)}
        for j in range(n):
            env["x"] = 2 ** j
            require(a[0] == "=", "atomic selector remains atomic")
            require(evaluate(a[1], env) == j + 10 and evaluate(a[2], env) == 0,
                    ("expanded selector endpoint", n, j))
            route_checks += 1
    for j in range(12):
        v, values = 2 ** j, [2 ** j]
        for _ in range(j + 1):
            v = 0 if v % 2 else 3 * v // 2
            values.append(v)
        require(values[-1] == 0 and all(v > 0 for v in values[:-1]), "route")
        routes.append({"leaf": j, "route": values})
    semantic_checks = 0
    for ranks in ((0, 1), (1, 2), (0, 2, 1)):
        operands = sorted([example(j, r) for j, r in enumerate(ranks)],
                          key=rank, reverse=True)
        a = selector(x, operands)
        for values in product(range(3), repeat=len(ranks)):
            env = {"a" + str(j): value for j, value in enumerate(values)}
            for j, target in enumerate(operands):
                env["x"] = 2 ** j
                require(bounded_truth(a, env) == bounded_truth(target, env),
                        ("bounded semantic endpoint", ranks, values, j))
                semantic_checks += 1
    report = {"status": "all computational checks passed",
              "warning": "Numerical checks and tree counts are not a formal proof of native derivability.",
              "source_commit": "1156099ffe30f7497d2c11ab20271f46cffcd115",
              "fully_expanded_term_sizes": sizes,
              "arithmetic_checks": arithmetic_checks,
              "block_count_and_scope_checks": count_checks,
              "exhaustive_small_padding_checks": padding_checks,
              "expanded_term_endpoint_checks": route_checks,
              "bounded_semantics_endpoint_checks": semantic_checks,
              "rank_zero_block_sizes": rows, "integer_route_witnesses": routes}
    output = Path(__file__).with_name("fused_finite_blocks_results.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
