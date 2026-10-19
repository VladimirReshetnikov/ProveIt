#!/usr/bin/env python3
"""Finite diagnostics for label_twist_obstruction.md.

The 16-element carrier is V_4 in Ackermann coding. It is not a model of
CP/GIC. CP/GIC validity in the note is an infinite ZFC proof. The transport
tests below check only the explicit set identities used in that proof.
"""
from __future__ import annotations

from itertools import product
from math import isqrt
from pathlib import Path
import argparse
import json


D = tuple(range(16))
LABELS = range(3)
E, U, A, B, SINGLE_B = 0, 1, 2, 3, 8


def mem(x: int, y: int) -> bool:
    return bool((y >> x) & 1)


def elems(s: int):
    return (x for x in D if mem(x, s))


def rank(s: int) -> int:
    return max((rank(x) + 1 for x in elems(s)), default=0)


def pi(x: int) -> int:
    return B if x == A else A if x == B else x


def pair(x: int, y: int) -> int:
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n: int) -> tuple[int, int]:
    d = (isqrt(8 * n + 1) - 1) // 2
    y = n - d * (d + 1) // 2
    return d - y, y


def imp(a: bool, b: bool) -> bool:
    return not a or b


def wim(a: int, b: int) -> int:
    return 4 * pair(a, b)


def wel(a: int, b: int) -> int:
    return 4 * pair(a, b) + 1


def wal(a: int, b: int) -> int:
    return 4 * pair(a, b) + 2


def weq(a: int, b: int) -> int:
    return 4 * pair(a, b) + 3


def wn(a: int) -> int:
    return wim(a, 1)


def wex(a: int, b: int) -> int:
    return wn(wal(a, wn(b)))


def update(s: tuple[int, ...], i: int, x: int) -> tuple[int, ...]:
    q = list(s)
    q[i] = x
    return tuple(q)


class Model:
    def __init__(self, gmask: int = 0, fmask: int = 0):
        self.gmask = gmask
        self.fmask = fmask

    def g(self, i: int, x: int) -> int:
        return pi(x) if ((self.gmask >> i) & 1) else x

    def f(self, i: int, x: int) -> int:
        return pi(x) if ((self.fmask >> i) & 1) else x

    def rel(self, i: int, j: int, s: tuple[int, ...]) -> bool:
        return mem(self.g(i, s[i]), self.f(j, s[j]))

    def evaluate(self, code: int, s: tuple[int, ...]) -> bool:
        if code == 0:
            return True
        tag = code % 4
        x, y = unpair(code // 4)
        if tag == 0:
            return imp(self.evaluate(x, s), self.evaluate(y, s))
        if tag == 1:
            return self.rel(x, y, s)
        if tag == 2:
            return all(self.evaluate(y, update(s, x, z)) for z in D)
        return s[x] == s[y]

    def image(self, which: str, i: int, s: int) -> int:
        fun = self.g if which == "g" else self.f
        return sum(1 << fun(i, x) for x in elems(s))


def main() -> dict:
    for x in D:
        assert pi(pi(x)) == x
        assert rank(pi(x)) == rank(x)
    assert rank(A) == rank(B) == 2 and A != B
    assert mem(E, B) and not mem(E, A)
    assert mem(B, SINGLE_B) and not mem(A, SINGLE_B)

    rho3 = wim(weq(0, 1), wim(wel(2, 0), wel(2, 1)))
    rho5 = wim(weq(0, 1), wim(wel(0, 2), wel(1, 2)))
    right = Model(gmask=0, fmask=2)
    left = Model(gmask=2, fmask=0)
    right_s = (B, B, E)
    left_s = (B, B, SINGLE_B)
    assert not right.evaluate(rho3, right_s)
    assert not left.evaluate(rho5, left_s)

    retained_congruence = equality_euclid = equality_existence = 0
    membership_vacuity = equality_vacuity = diagonal = 0
    valuations = tuple(product(D, repeat=3))
    for model, missing in ((right, 3), (left, 5)):
        for s in valuations:
            assert model.evaluate(0, s)
            assert not model.evaluate(1, s)
            assert model.evaluate(wim(0, 0), s)
            for i in LABELS:
                assert not model.rel(i, i, s)
                diagonal += 1
            for a, b, c in product(LABELS, repeat=3):
                if missing == 3:
                    keep = imp(s[c] == s[a],
                               imp(model.rel(c, b, s), model.rel(a, b, s)))
                else:
                    keep = imp(s[a] == s[b],
                               imp(model.rel(c, a, s), model.rel(c, b, s)))
                assert keep
                retained_congruence += 1
                assert imp(s[c] == s[a], imp(s[c] == s[b], s[a] == s[b]))
                equality_euclid += 1
                if c != a and c != b:
                    assert all(model.rel(a, b, update(s, c, z))
                               == model.rel(a, b, s) for z in D)
                    membership_vacuity += 1
                    assert all((update(s, c, z)[a] == update(s, c, z)[b])
                               == (s[a] == s[b]) for z in D)
                    equality_vacuity += 1
            for a, b in product(LABELS, repeat=2):
                assert any(update(s, a, z)[a] == update(s, a, z)[b] for z in D)
                equality_existence += 1

    # Six representative formulas, retaining the true/false aliases and
    # both coordinates of the twisted atoms. These are finite diagnostics,
    # not exhaustive checks of all formulas.
    formulas = (
        0, 1, wel(0, 1), wel(1, 2), weq(0, 2),
        wim(wel(2, 1), wel(0, 2)),
    )
    sample_vals = tuple(product((0, 1, 2, 3, 8), repeat=3))
    commutation = exists_all = distribution = lukasiewicz = 0
    for model in (left, right):
        for s in sample_vals:
            for a, b in product(LABELS, repeat=2):
                for phi in formulas:
                    lhs = model.evaluate(wal(a, wal(b, phi)), s)
                    rhs = model.evaluate(wal(b, wal(a, phi)), s)
                    assert imp(lhs, rhs)
                    commutation += 1
            for a in LABELS:
                for phi in formulas:
                    assert imp(model.evaluate(wex(a, wal(a, phi)), s),
                               model.evaluate(phi, s))
                    exists_all += 1
                for phi, psi in product(formulas, repeat=2):
                    assert imp(model.evaluate(wal(a, wim(phi, psi)), s),
                               imp(model.evaluate(wal(a, phi), s),
                                   model.evaluate(wal(a, psi), s)))
                    distribution += 1
    for a, b, c, u in product((False, True), repeat=4):
        assert imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
        lukasiewicz += 1

    # Exact finite instances of the power-bound and image-transport
    # identities from Sections 5-6. All maps are involutions here.
    power_transport = image_transport = 0
    triples = tuple(p for p in product(LABELS, repeat=3) if len(set(p)) == 3)
    for gmask, fmask in product(range(8), repeat=2):
        model = Model(gmask, fmask)
        for a, b, c in triples:
            for x in range(4):
                base = model.f(a, x)
                candidates = tuple(y for y in D
                                   if (model.f(b, y) & ~base) == 0)
                k = sum(1 << model.g(b, y) for y in candidates)
                w = model.f(c, k)  # inverse(f_c)=f_c
                assert model.f(c, w) == k
                assert rank(k) <= rank(x) + 1
                assert rank(w) == rank(k)
                for y in D:
                    subset = all(not mem(model.g(c, z), model.f(b, y))
                                 or mem(model.g(c, z), base) for z in D)
                    assert subset == (y in candidates)
                    if subset:
                        assert mem(model.g(b, y), model.f(c, w))
                power_transport += 1
            for selected in D:
                image = model.image("g", b, selected)
                c_value = model.f(c, image)
                assert all(mem(model.g(b, y), model.f(c, c_value))
                           == mem(y, selected) for y in D)
                image_transport += 1

    return {
        "status": "PASS",
        "carrier": "V_4, 16 objects in Ackermann encoding",
        "rank_preserving_transposition": {"A": A, "B": B, "rank": 2},
        "targets": {
            "rho3_0_1_2": {"code": rho3, "valuation": list(right_s),
                          "value": False, "gmask": 0, "fmask": 2},
            "rho5_1_2_0": {"code": rho5, "valuation": list(left_s),
                          "value": False, "gmask": 2, "fmask": 0},
        },
        "checks": {
            "retained_congruence": retained_congruence,
            "euclidean_equality": equality_euclid,
            "equality_existence": equality_existence,
            "membership_vacuity": membership_vacuity,
            "equality_vacuity": equality_vacuity,
            "diagonal_falsity": diagonal,
            "quantifier_commutation_samples": commutation,
            "exists_all_samples": exists_all,
            "distribution_samples": distribution,
            "lukasiewicz_truth_assignments": lukasiewicz,
            "power_transport_instances": power_transport,
            "image_transport_instances": image_transport,
        },
        "scope": [
            "Finite logical diagnostics and exact finite transport identities.",
            "No finite CP/GIC model is asserted or tested.",
            "The infinite CP/GIC argument is proved in label_twist_obstruction.md.",
            "No Lean formalization, state reduction, or consistency-strength separation is claimed.",
        ],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = main()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")

