"""Finite checks of outgoing-profile equality and the reserved-zero translation.

No finite relation in this program is claimed to model PSC or EPSC.  The
exhaustive part checks the local singleton lemma on arbitrary finite relations.
The translation checks use finite structures satisfying its weaker hypotheses.
The paper supplies the unbounded proofs.  Python recursion limits apply to the
diagnostic formula evaluator; this is not the proposed proof-search machine.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path

BOT = ("bot",)
F = ("r", 0, 0)


def rel(a, b):
    return ("r", a, b)


def eq(a, b):
    return ("eq", a, b)


def imp(a, b):
    return ("imp", a, b)


def all_(a, b):
    return ("all", a, b)


def translate(p):
    """Shift every source variable by one; reserve zero for the proxy and F."""
    tag = p[0]
    if tag == "bot":
        return F
    if tag == "r":
        return rel(p[1] + 1, p[2] + 1)
    if tag == "eq":
        return all_(0, imp(rel(p[1] + 1, 0), rel(p[2] + 1, 0)))
    if tag == "imp":
        return imp(translate(p[1]), translate(p[2]))
    if tag == "all":
        return all_(p[1] + 1, translate(p[2]))
    raise ValueError(p)


def nodes(p):
    if p[0] in ("bot", "r", "eq"):
        return 1
    if p[0] == "all":
        return 1 + nodes(p[2])
    return 1 + nodes(p[1]) + nodes(p[2])


def profiles(n, bits):
    mask = (1 << n) - 1
    rows = tuple((bits >> (a * n)) & mask for a in range(n))
    cols = tuple(sum(((rows[a] >> b) & 1) << a for a in range(n))
                 for b in range(n))
    twins = tuple(sum((rows[a] == rows[b] and cols[a] == cols[b]) << b
                     for b in range(n)) for a in range(n))
    return rows, cols, twins


def evaluate(p, rows, env, twins=None):
    tag = p[0]
    if tag == "bot":
        return False
    if tag == "r":
        return bool((rows[env[p[1]]] >> env[p[2]]) & 1)
    if tag == "eq":
        if twins is None:
            raise ValueError("No source equality interpretation supplied")
        return bool((twins[env[p[1]]] >> env[p[2]]) & 1)
    if tag == "imp":
        return not evaluate(p[1], rows, env, twins) or evaluate(p[2], rows, env, twins)
    if tag == "all":
        return all(evaluate(p[2], rows, {**env, p[1]: a}, twins)
                   for a in range(len(rows)))
    raise ValueError(p)


def gamma(n):
    s = bin(n + 1)[2:]
    return "0" * (len(s) - 1) + s


def encode(p):
    """Prefix tags: 00 relation, 01 implication, 1 universal; gamma fields."""
    if p[0] == "r":
        return "00" + gamma(p[1]) + gamma(p[2])
    if p[0] == "imp":
        return "01" + encode(p[1]) + encode(p[2])
    if p[0] == "all":
        return "1" + gamma(p[1]) + encode(p[2])
    raise ValueError("Only target formulas have this codec")


def decode(word):
    """Total iterative parser on finite binary strings; None means malformed."""
    if any(b not in "01" for b in word):
        return None
    pos = 0
    stack = []
    value = None

    def natural():
        nonlocal pos
        start = pos
        while pos < len(word) and word[pos] == "0":
            pos += 1
        zeros = pos - start
        if pos + zeros + 1 > len(word):
            raise ValueError("short natural")
        out = int(word[pos:pos + zeros + 1], 2) - 1
        pos += zeros + 1
        return out

    try:
        while True:
            if value is None:
                if pos >= len(word):
                    return None
                bit = word[pos]
                pos += 1
                if bit == "1":
                    stack.append(("all", natural()))
                    continue
                if pos >= len(word):
                    return None
                bit = word[pos]
                pos += 1
                if bit == "0":
                    value = rel(natural(), natural())
                else:
                    stack.append(("left",))
                    continue
            if not stack:
                return value if pos == len(word) else None
            frame = stack.pop()
            if frame[0] == "all":
                value = all_(frame[1], value)
            elif frame[0] == "left":
                stack.append(("right", value))
                value = None
            else:
                value = imp(frame[1], value)
    except ValueError:
        return None


def random_formula(rng, depth):
    choice = rng.randrange(5 if depth else 3)
    if choice == 0:
        return BOT
    if choice == 1:
        return rel(rng.randrange(3), rng.randrange(3))
    if choice == 2:
        return eq(rng.randrange(3), rng.randrange(3))
    if choice == 3:
        return imp(random_formula(rng, depth - 1), random_formula(rng, depth - 1))
    return all_(rng.randrange(3), random_formula(rng, depth - 1))


def run():
    graph_count = local_roots = comparisons = global_models = 0
    frame_pool = []
    per_size = []
    for n in range(1, 5):
        local_before, global_before = local_roots, global_models
        for bits in range(1 << (n * n)):
            graph_count += 1
            rows, cols, twins = profiles(n, bits)
            roots = [a for a in range(n) if twins[a] in cols]
            local_roots += len(roots)
            for a in roots:
                for b in range(n):
                    e = (rows[a] & ~rows[b]) == 0
                    o = bool((twins[a] >> b) & 1)
                    if e != o:
                        raise AssertionError((n, bits, a, b))
                    comparisons += 1
            if len(roots) == n:
                global_models += 1
                false_points = [a for a in range(n) if not ((rows[a] >> a) & 1)]
                if false_points:
                    frame_pool.append((n, bits, false_points[0]))
        per_size.append({"size": n, "relations": 1 << (n * n),
                         "local_singleton_roots": local_roots - local_before,
                         "global_singleton_structures": global_models - global_before})

    rng = random.Random(20261016)
    frames = rng.sample(frame_pool, min(32, len(frame_pool)))
    formulas = [BOT, eq(0, 1), all_(0, eq(0, 0)),
                all_(0, imp(rel(0, 1), all_(1, eq(0, 1)))),
                imp(all_(0, rel(0, 0)), rel(1, 1)),
                all_(0, imp(BOT, all_(1, BOT)))]
    formulas += [random_formula(rng, 4) for _ in range(400)]
    translation_checks = 0
    for n, bits, point in frames:
        rows, cols, twins = profiles(n, bits)
        for p in formulas:
            q = translate(p)
            if decode(encode(q)) != q:
                raise AssertionError("codec round trip")
            for _ in range(4):
                env = {a: rng.randrange(n) for a in range(3)}
                translated_env = {0: point, **{a + 1: v for a, v in env.items()}}
                if evaluate(p, rows, env, twins) != evaluate(q, rows, translated_env):
                    raise AssertionError((n, bits, point, p, env))
                translation_checks += 1

    # No-shift capture: in the 2-cycle, equality of its two objects is false,
    # while forall v0 (R(v0,v0) -> R(v1,v0)) is true.
    rows, cols, twins = profiles(2, 6)
    source = eq(0, 1)
    unsafe = all_(0, imp(rel(0, 0), rel(1, 0)))
    env = {0: 0, 1: 1}
    assert not evaluate(source, rows, env, twins)
    assert evaluate(unsafe, rows, env)
    assert not evaluate(translate(source), rows, {0: 0, 1: 0, 2: 1})

    # GEN v0 is unsound for a pointed false parameter.  This relation has a
    # 2-cycle and one self-loop; it has all observational singletons.
    rows, cols, twins = profiles(3, (1 << 1) | (1 << 3) | (1 << 8))
    a = imp(F, rel(1, 1))
    assert evaluate(a, rows, {0: 0, 1: 0})
    assert not evaluate(all_(0, a), rows, {0: 0, 1: 0})

    words = parsed = 0
    for length in range(15):
        for tup in itertools.product("01", repeat=length):
            word = "".join(tup)
            p = decode(word)
            words += 1
            if p is not None:
                parsed += 1
                assert encode(p) == word

    return {
        "status": "finite checks passed; unbounded theorems are proved in the report",
        "scope": "No tested finite structure is asserted to satisfy PSC/EPSC.",
        "relations": graph_count, "local_singleton_roots": local_roots,
        "local_E_iff_O_comparisons": comparisons,
        "global_singleton_structures": global_models,
        "pointed_frame_pool": len(frame_pool), "translation_frames": len(frames),
        "formulas": len(formulas), "translation_checks": translation_checks,
        "prefix_words": words, "parsed_complete_words": parsed,
        "negative_controls": {"unshifted_proxy_capture": "rejected",
                              "generalization_at_reserved_zero": "rejected"},
        "proxy_formula_nodes": nodes(translate(eq(0, 1))),
        "proxy_example_bits": encode(translate(eq(0, 1))),
        "falsity_bits": encode(F), "per_size": per_size,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O: diagnostic assertions must be enabled")
    result = run()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
