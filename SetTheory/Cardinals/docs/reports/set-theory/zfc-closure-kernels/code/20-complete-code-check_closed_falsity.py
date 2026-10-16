#!/usr/bin/env python3
"""Independent finite regressions for the closed-universal-bottom proposal.

This is a mathematical reference artifact, not a proof checker or TM compiler.
All reported formula codes use the unchanged project base-three Cantor codec.
"""
from __future__ import annotations

# Released under MIT-0; see ../LICENSE.txt.

from functools import lru_cache
from itertools import product
from math import isqrt
import argparse
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O/-OO: the regression checks require assertions")

TOP = ("top",)
BOT = ("bot",)

def rel(a, b): return ("rel", a, b)
def imp(a, b): return ("imp", a, b)
def all_(v, a): return ("all", v, a)

# The orientation minimizes the numeric code among the four choices on 0,1.
Q = all_(1, all_(0, rel(1, 0)))

def neg_q(a): return imp(a, Q)
def ex_q(v, a): return neg_q(all_(v, neg_q(a)))

@lru_cache(maxsize=None)
def free_vars(a):
    if a[0] in ("top", "bot"): return frozenset()
    if a[0] == "rel": return frozenset(a[1:])
    if a[0] == "imp": return free_vars(a[1]) | free_vars(a[2])
    if a[0] == "all": return free_vars(a[2]) - {a[1]}
    raise ValueError(a)

@lru_cache(maxsize=None)
def has_off_diagonal(a):
    if a[0] == "rel": return a[1] != a[2]
    if a[0] == "imp": return has_off_diagonal(a[1]) or has_off_diagonal(a[2])
    if a[0] == "all": return has_off_diagonal(a[2])
    return False

def translate(a):
    if a == BOT: return Q
    if a[0] in ("top", "rel"): return a
    if a[0] == "imp": return imp(translate(a[1]), translate(a[2]))
    if a[0] == "all": return all_(a[1], translate(a[2]))
    raise ValueError(a)

def evaluate(a, n, graph, env):
    if a == TOP: return True
    if a == BOT: return False
    if a[0] == "rel": return bool(graph & (1 << (env[a[1]] * n + env[a[2]])))
    if a[0] == "imp": return not evaluate(a[1], n, graph, env) or evaluate(a[2], n, graph, env)
    if a[0] == "all": return all(evaluate(a[2], n, graph, env | {a[1]: x}) for x in range(n))
    raise ValueError(a)

def pair(a, b): return (a + b) * (a + b + 1) // 2 + b

def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b

def encode(a):
    if a == TOP: return 0
    if a[0] == "rel": return 3 * pair(a[1], a[2]) + 1
    if a[0] == "imp": return 3 * pair(encode(a[1]), encode(a[2]))
    if a[0] == "all": return 3 * pair(a[1], encode(a[2])) + 2
    raise ValueError("The positive codec has no primitive bottom")

@lru_cache(maxsize=None)
def decode(n):
    if n == 0: return TOP
    p, tag = divmod(n, 3)
    a, b = unpair(p)
    if tag == 0: return imp(decode(a), decode(b))
    if tag == 1: return rel(a, b)
    return all_(a, decode(b))

def run():
    assert free_vars(Q) == frozenset()
    orientations = []
    for i, j in ((0, 1), (1, 0)):
        for outer, inner in ((0, 1), (1, 0)):
            f = all_(outer, all_(inner, rel(i, j)))
            orientations.append({"atom": [i, j], "outer_inner_binders": [outer, inner], "code": encode(f)})
    assert encode(Q) == 3239
    first_closed_offdiag = next(n for n in range(3240) if not free_vars(decode(n)) and has_off_diagonal(decode(n)))
    assert first_closed_offdiag == 3239
    for n in range(3240):
        assert encode(decode(n)) == n

    # Include bottom-bearing, negative, mixed-variable and shadowed examples.
    atoms = [BOT, TOP] + [rel(i, j) for i, j in product(range(2), repeat=2)]
    formulas = list(atoms)
    formulas += [imp(a, b) for a, b in product(atoms, repeat=2)]
    formulas += [all_(v, a) for v, a in product(range(2), atoms)]
    formulas += [all_(v, imp(a, b)) for v, a, b in product(range(2), atoms, atoms)]
    formulas += [imp(all_(v, a), all_(w, b)) for v, w, a, b in product(range(2), range(2), atoms, atoms)]
    formulas += [all_(v, all_(v, imp(a, BOT))) for v, a in product(range(2), atoms)]
    translation_cases = explosion_cases = 0
    for n in (1, 2):
        for graph in range(1 << (n * n)):
            q = evaluate(Q, n, graph, {})
            assert q == (graph == (1 << (n * n)) - 1)
            for a in formulas:
                t = translate(a)
                assert free_vars(t) == free_vars(a)
                for values in product(range(n), repeat=2):
                    env = dict(enumerate(values))
                    actual = evaluate(t, n, graph, env)
                    assert actual == (True if q else evaluate(a, n, graph, env))
                    translation_cases += 1
                    # Every translated formula belongs to the positive language.
                    assert (not q) or actual
                    explosion_cases += 1

    empty_q = ex_q(0, all_(1, imp(rel(1, 0), Q)))
    diagonal = all_(0, rel(0, 0))
    target_implication = imp(empty_q, imp(diagonal, Q))
    target_cases = 0
    for n in (1, 2, 3):
        for graph in range(1 << (n * n)):
            assert evaluate(target_implication, n, graph, {})
            target_cases += 1

    return {
        "scope": "Finite regressions plus exact arithmetic; no infinite-model proof, proof checker, compiler, TM table or state claim.",
        "Q": "forall v1 forall v0 E(v1,v0)",
        "Q_code": encode(Q),
        "Q_constructor_macros": ["one", "zero", "one", "zero", "rel", "all", "all"],
        "orientation_codes": orientations,
        "minimum_closed_offdiagonal_code_census": {"codes_examined": 3240, "minimum": first_closed_offdiag},
        "encoding_roundtrips": 3240,
        "translation_cases": translation_cases,
        "explosion_cases": explosion_cases,
        "virtual_empty_diagonal_implication_graphs": target_cases,
        "proof_obligation": "The manuscript proves structural translation, the target theorem, and the narrow numeric-code minimum; these finite checks are independent regressions only."
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "closed_falsity_checks.json")
    args = parser.parse_args()
    result = run()
    path = args.output
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
