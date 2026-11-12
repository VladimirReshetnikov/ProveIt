"""Independent de Bruijn checks of weak-head normalization laws.

No imports from the implementation under review. These finite checks do
not prove strong normalization or the calculus equivalence theorem.
"""

from functools import lru_cache
import json
import random

ZERO = ("z",)


def v(i):
    return ("v", i)


def s(t):
    return ("s", t)


def it(n, a, h):
    return ("i", n, a, h)


def shift(t, amount=1, cutoff=0):
    if t[0] == "v":
        return v(t[1] + amount) if t[1] >= cutoff else t
    if t[0] == "z":
        return t
    if t[0] == "s":
        return s(shift(t[1], amount, cutoff))
    return it(shift(t[1], amount, cutoff), shift(t[2], amount, cutoff),
              shift(t[3], amount, cutoff + 1))


def subst(t, sigma):
    if t[0] == "v":
        return sigma(t[1])
    if t[0] == "z":
        return t
    if t[0] == "s":
        return s(subst(t[1], sigma))
    return it(subst(t[1], sigma), subst(t[2], sigma),
              subst(t[3], lambda i: v(0) if i == 0 else shift(sigma(i - 1))))


def plug(h, t):
    return subst(h, lambda i: t if i == 0 else v(i - 1))


def step(t):
    """One deterministic head step, or None if head normal."""
    if t[0] != "i":
        return None
    n, a, h = t[1:]
    if n[0] == "z":
        return a
    if n[0] == "s":
        return plug(h, it(n[1], a, h))
    n1 = step(n)
    return None if n1 is None else it(n1, a, h)


@lru_cache(maxsize=None)
def weak(t):
    for _ in range(100000):
        nxt = step(t)
        if nxt is None:
            return t
        t = nxt
    raise RuntimeError("finite test exceeded its explicit reduction budget")


def selector(c, a, b):
    return it(c, a, shift(b))


def parity(c):
    return it(c, ZERO, selector(v(0), s(ZERO), ZERO))


def gen(rng, scope, depth):
    if depth == 0 or rng.randrange(5) < 2:
        return ZERO if rng.randrange(scope + 1) == scope else v(rng.randrange(scope))
    if rng.randrange(3) == 0:
        return s(gen(rng, scope, depth - 1))
    return it(gen(rng, scope, depth - 1), gen(rng, scope, depth - 1),
              gen(rng, scope + 1, depth - 1))


def run():
    rng = random.Random(20261112)
    counts = {"idempotence": 0, "left_substitution_coherence": 0,
              "head_step_substitution_stability": 0, "packet_rows": 0}
    for _ in range(2500):
        t = gen(rng, 2, 3)
        replacements = [gen(rng, 2, 2), gen(rng, 2, 2)]
        sigma = replacements.__getitem__
        w = weak(t)
        assert weak(w) == w
        counts["idempotence"] += 1
        assert weak(subst(w, sigma)) == weak(subst(t, sigma))
        counts["left_substitution_coherence"] += 1
        nxt = step(t)
        if nxt is not None:
            assert step(subst(t, sigma)) == subst(nxt, sigma)
            counts["head_step_substitution_stability"] += 1

    for _ in range(300):
        # H has a distinguished hole 0 and two passive parameters 1,2.
        h = gen(rng, 3, 2)
        t = gen(rng, 2, 2)
        u = gen(rng, 2, 2)
        # Packet scope: y=0, x=1, passive parameters=2,3.
        hx = subst(h, lambda i: v(1) if i == 0 else v(i + 1))
        p = parity(v(0))
        left = selector(v(0), ZERO, selector(p, v(1), hx))
        right = selector(v(0), ZERO, selector(p, shift(t, 2), shift(u, 2)))
        rows = [(weak(plug(left, n)), weak(plug(right, n)))
                for n in (ZERO, s(ZERO), s(s(ZERO)))]
        assert rows[0] == (ZERO, ZERO)
        assert rows[1] == (weak(h), weak(shift(u)))
        assert rows[2] == (v(0), weak(shift(t)))
        counts["packet_rows"] += 3

    raw = it(ZERO, v(0), v(0))
    raw_in_successor = weak(s(raw))
    normal_in_successor = weak(s(weak(raw)))
    assert raw_in_successor != normal_in_successor
    # The companion falsely strong law for normalized substitution ranges.
    h = s(v(0))
    sigma = lambda _: raw
    sigma_w = lambda _: weak(raw)
    assert weak(subst(h, sigma)) != weak(subst(h, sigma_w))
    return {
        "status": "all finite checks passed",
        "checks": counts,
        "total": sum(counts.values()),
        "right_congruence_is_not_syntactic": True,
        "normalizing_substitution_ranges_changes_the_result": True,
        "counterexample_left": raw_in_successor,
        "counterexample_right": normal_in_successor,
        "scope": "Finite deterministic regression checks, independent implementation; not a formal metatheoretic proof."
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
