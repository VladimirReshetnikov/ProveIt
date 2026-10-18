"""Finite semantic controls for two theorem-level C254 compiler changes.

This standalone program does not simulate a binary Turing machine.  Formula
codes are the exact base-four / dual-Cantor codes used in the source.  Zero
has its specified truth meaning, rather than an infinitely unfolding parse.
All numbers are exact Python integers; no fingerprint arithmetic is used.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import product
from math import isqrt
import json
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def code(tag: int, a: int, b: int) -> int:
    return 4 * pair(a, b) + tag


@lru_cache(maxsize=None)
def labels(n: int) -> frozenset[int]:
    if n == 0:
        return frozenset()
    a, b = unpair(n // 4)
    tag = n % 4
    if tag in (1, 3):
        return frozenset((a, b))
    if tag == 0:
        return labels(a) | labels(b)
    return frozenset((a,)) | labels(b)


def evaluate(n: int, env: dict[int, int], size: int, rel: int) -> bool:
    if n == 0:
        return True
    a, b = unpair(n // 4)
    tag = n % 4
    if tag == 0:
        return not evaluate(a, env, size, rel) or evaluate(b, env, size, rel)
    if tag == 1:
        return bool(rel & (1 << (size * env[a] + env[b])))
    if tag == 3:
        return env[a] == env[b]
    return all(evaluate(b, env | {a: v}, size, rel) for v in range(size))


def valid(n: int, size: int, rel: int) -> bool:
    keys = sorted(labels(n))
    return all(evaluate(n, dict(zip(keys, vals)), size, rel)
               for vals in product(range(size), repeat=len(keys)))


def irreflexive_relations(size: int):
    positions = [(a, b) for a in range(size) for b in range(size) if a != b]
    for word in range(1 << len(positions)):
        yield sum(1 << (size * a + b) for j, (a, b) in enumerate(positions)
                  if word & (1 << j))


def nip_residue_clear(h: int) -> tuple[bool, int, int]:
    """Literal four-test drain: (halted, residual cache, decrement tests)."""
    tests = 0
    while True:
        for residue in range(4):
            tests += 1
            if h == 0:
                return residue == 1, 0, tests
            h -= 1


def run_controls() -> dict:
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled; do not use Python -O or -OO.")
    counts = dict(codec=0, atomic_target=0, odd_code_rigidity=0,
                  generalized_mp=0, generalized_mp_valid_premises=0,
                  drain=0)

    for n in range(10000):
        assert pair(*unpair(n)) == n
        counts["codec"] += 1

    for size in (1, 2, 3):
        for rel in irreflexive_relations(size):
            for i in range(8):
                for j in range(8):
                    assert not valid(code(1, i, j), size, rel)
                    counts["atomic_target"] += 1

    # The theorem-level MP lemma needs an irreflexive domain with >=2 objects.
    # These are controls for its semantic premises, not finite models of CP/GIC.
    for size in (2, 3):
        for rel in irreflexive_relations(size):
            validity = {n: valid(n, size, rel) for n in range(24)}
            for n in range(1, 257, 2):
                a, b = unpair(n // 4)
                diagonal = n % 4 == 3 and a == b
                assert valid(n, size, rel) == diagonal
                counts["odd_code_rigidity"] += 1
            for a in range(24):
                for b in range(24):
                    for tag in range(4):
                        h = code(tag, a, b)
                        if validity[a] and valid(h, size, rel):
                            assert validity[b]
                            counts["generalized_mp_valid_premises"] += 1
                        counts["generalized_mp"] += 1

    # The larger target includes the old target exactly and clears every other
    # input; the formula gives its complete clock, including the final zero test.
    for h in range(10000):
        halt, residual, tests = nip_residue_clear(h)
        assert halt == (h % 4 == 1)
        assert residual == 0 and tests == h + 1
        counts["drain"] += 1

    # This necessity control is deliberately a one-element irreflexive model.
    # It is not a NativeAx model: CP forbids such a model.
    a, b = 0, 1
    eq_ab = code(3, a, b)
    assert valid(a, 1, 0) and valid(eq_ab, 1, 0) and not valid(b, 1, 0)

    # The rule is about theorems, not truths at one assignment.  Even on a
    # two-element irreflexive domain a true equality at one assignment does not
    # suffice for the claimed conclusion.
    same_env = {0: 0, 1: 0}
    assert evaluate(a, same_env, 2, 0)
    assert evaluate(eq_ab, same_env, 2, 0)
    assert not evaluate(b, same_env, 2, 0)

    # Genuine safe additions to the MP acceptance set.  Both conclusions are
    # reflexivity, code3; ordinary MP would reject these non-implication caches.
    examples = [dict(top=0, conclusion=3, cache=code(2, 0, 3), tag=2),
                dict(top=3, conclusion=3, cache=code(3, 3, 3), tag=3)]
    for ex in examples:
        assert ex["cache"] != code(0, ex["top"], ex["conclusion"])
        for rel in irreflexive_relations(2):
            assert valid(ex["top"], 2, rel)
            assert valid(ex["cache"], 2, rel)
            assert valid(ex["conclusion"], 2, rel)

    return dict(status="PASS", counts=counts, examples=examples,
                singleton_counterexample=dict(top=a, conclusion=b, cache=eq_ab),
                scope="finite semantic and scalar controls; no TM or PA theorem")


if __name__ == "__main__":
    result = run_controls()
    output = Path(__file__).with_name("semantic-targets-results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
