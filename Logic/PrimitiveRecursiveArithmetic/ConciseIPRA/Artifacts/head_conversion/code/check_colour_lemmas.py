"""Finite checks of the elementary lemmas in the raw-VS obstruction.

This is not a decision procedure for native derivability or a formal proof
of the universal soundness theorem. Quantifiers are checked on {0,1,2};
the report supplies the unbounded mathematical argument separately.
"""

from itertools import product
import json

NUMBERS = range(3)
COLOURS = range(3)
Z = ("0",)


def var(x):
    return ("v", x)


def succ(t):
    return ("s", t)


def it(n, a, h):
    return ("i", n, a, h)


def number(t, rho):
    tag = t[0]
    if tag == "v":
        return rho[t[1]][0]
    if tag == "0":
        return 0
    if tag == "s":
        return number(t[1], rho) + 1
    state = number(t[2], rho)
    for _ in range(number(t[1], rho)):
        state = number(t[3], dict(rho, r=(state, 0)))
    return state


def value(t, rho):
    return rho[t[1]] if t[0] == "v" else (number(t, rho), 0)


def related(v, w):
    return v[0] == w[0] and (not v[1] or not w[1] or v[1] == w[1])


def subst(t, x, replacement):
    if t[0] == "v":
        return replacement if t[1] == x else t
    if t[0] == "0":
        return t
    if t[0] == "s":
        return succ(subst(t[1], x, replacement))
    return it(subst(t[1], x, replacement), subst(t[2], x, replacement),
              t[3] if x == "r" else subst(t[3], x, replacement))


def truth(a, rho):
    if a[0] == "=":
        return related(value(a[1], rho), value(a[2], rho))
    if a[0] == "q":
        _, y, body = a
        base = truth(body, dict(rho, **{y: (0, 0)}))
        return not base or all(truth(body, dict(rho, **{y: (n, 0)}))
                               for n in NUMBERS)
    _, x, y, body = a
    return any(truth(("q", y, body), dict(rho, **{x: (n, 0)}))
               for n in NUMBERS)


def vals(names, colours):
    for ns in product(NUMBERS, repeat=len(names)):
        for cs in product(colours, repeat=len(names)):
            yield dict(zip(names, zip(ns, cs)))


def run():
    a, b, y, r = map(var, ("a", "b", "y", "r"))
    terms = [a, b, Z, succ(Z), succ(a), succ(b),
             it(Z, a, r), it(succ(Z), a, r),
             it(a, Z, succ(r)), it(b, a, b),
             it(a, b, Z), it(b, b, succ(r))]
    matrix_terms = terms + [y, succ(y), it(y, a, r), it(a, y, Z)]
    matrices = [("=", u, v) for u in matrix_terms for v in matrix_terms]
    counts = {"variable_substitution": 0, "compound_recolouring": 0,
              "atomic_coloured_lift": 0, "universal_neutral_lift": 0}

    for rho in vals(("a", "b"), (1, 2)):
        for x in ("a", "b"):
            for t in terms:
                if not related(rho[x], value(t, rho)):
                    continue
                for u in terms:
                    for v in terms:
                        if related(value(u, rho), value(v, rho)):
                            assert related(value(v, rho), value(subst(u, x, t), rho))
                            counts["variable_substitution"] += 1

    compounds = [("q", "y", e) for e in matrices]
    compounds += [("d", "a", "y", e) for e in matrices]
    compounds += [("q", "b", q) for q in compounds[::31]]
    compounds += [("d", "b", "y", q) for q in compounds[::37]]
    for rho in vals(("a", "b"), COLOURS):
        neutral = {x: (v[0], 0) for x, v in rho.items()}
        for f in compounds:
            assert truth(f, rho) == truth(f, neutral)
            counts["compound_recolouring"] += 1
        for e in matrices:
            for n in NUMBERS:
                if truth(e, dict(rho, y=(n, 0))):
                    assert any(truth(e, dict(rho, y=(n, c))) for c in (1, 2))
                    counts["atomic_coloured_lift"] += 1
            if all(truth(e, dict(rho, y=(n, 0))) for n in NUMBERS):
                for n, c in product(NUMBERS, (1, 2)):
                    assert truth(e, dict(rho, y=(n, c)))
                    counts["universal_neutral_lift"] += 1

    rho = {"a": (0, 1), "b": (0, 2)}
    assumption = ("=", it(Z, a, r), b)
    conclusion = ("=", a, b)
    assert truth(assumption, rho) and not truth(conclusion, rho)
    # The tempting variant allowing neutral free sources is unsound.
    x, u, v = (0, 0), (0, 1), (0, 2)
    assert related(x, u) and related(x, v) and not related(v, u)
    return {
        "status": "all finite checks passed",
        "checks": counts,
        "total": sum(counts.values()),
        "separating_assumption": True,
        "separating_conclusion": False,
        "neutral_source_counterexample_confirmed": True,
        "scope": "Finite semantic regression checks only; unbounded theorem is a written proof."
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
