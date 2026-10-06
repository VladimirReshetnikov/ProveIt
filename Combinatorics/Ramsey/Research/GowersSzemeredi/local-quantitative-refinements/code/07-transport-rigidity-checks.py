#!/usr/bin/env python3
"""Exact finite checks for transport-sensitive rigidity.

Python 3.10+, standard library only.  These are reproducible finite tests,
not a substitute for the general proofs and not Lean verification.
Run: python checks.py --output verification.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Sequence

SEED = 20261006


def profile(mu: Sequence[F], shift: int, t: F,
            root: Sequence[F] | None = None) -> F:
    """Exact fractional-knapsack transport profile on the support of mu."""
    if not 0 <= t <= 1 or sum(mu) != 1 or any(x < 0 for x in mu):
        raise ValueError("mu must be a probability vector and 0 <= t <= 1")
    nu = mu if root is None else root
    if len(nu) != len(mu) or sum(nu) != 1 or any(x < 0 for x in nu):
        raise ValueError("root must be a probability vector of the same length")
    if any(nu[i] and not mu[i] for i in range(len(mu))):
        raise ValueError("root must be supported on the support of mu")
    n = len(mu)
    items = sorted(((nu[(g-shift) % n] / w, w)
                    for g, w in enumerate(mu) if w), reverse=True)
    left, value = t, F(0)
    for ratio, capacity in items:
        take = min(left, capacity)
        value += ratio * take
        left -= take
        if not left:
            break
    return value


def dual_profile(mu: Sequence[F], shift: int, t: F,
                 root: Sequence[F] | None = None) -> F:
    """Independent exact evaluation of the one-dimensional dual formula."""
    nu = mu if root is None else root
    n = len(mu)
    candidates = {F(0)} | {nu[(g-shift) % n] / w
                              for g, w in enumerate(mu) if w}
    return min(lam*t + sum(max(F(0), nu[(g-shift) % n]-lam*w)
                           for g, w in enumerate(mu) if w)
               for lam in candidates)


def local_data(fibers: Sequence[Sequence[int]], support: set[int],
               labels: Sequence[int], hmod: int) -> tuple[list[F], list[F], list[F]]:
    """Return mu, directional defects, and directional boundary masses."""
    n = len(fibers)
    if not support or any(not fibers[g] for g in support):
        raise ValueError("support must be nonempty and consist of nonempty fibers")
    size = sum(len(fibers[g]) for g in support)
    mu = [F(len(fibers[g]), size) if g in support else F(0)
          for g in range(n)]
    defects, boundary = [], []
    for d in range(n):
        err, out = F(0), F(0)
        for g in support:
            target = (g+d) % n
            if target not in support:
                err += mu[g]
                out += mu[g]
            else:
                bad = sum((y-x-labels[d]) % hmod != 0
                          for x in fibers[g] for y in fibers[target])
                err += mu[g]*F(bad, len(fibers[g])*len(fibers[target]))
        defects.append(err)
        boundary.append(out)
    return mu, defects, boundary


def modal_labels(fibers: Sequence[Sequence[int]], support: set[int],
                 hmod: int) -> list[int]:
    n = len(fibers)
    size = sum(len(fibers[g]) for g in support)
    answer = []
    for d in range(n):
        mass = [F(0) for _ in range(hmod)]
        for g in support:
            target = (g+d) % n
            if target in support:
                unit = F(1, size*len(fibers[target]))
                for x in fibers[g]:
                    for y in fibers[target]:
                        mass[(y-x) % hmod] += unit
        answer.append(max(range(hmod), key=lambda a: mass[a]))
    return answer


def word_cost(mu: Sequence[F], defects: Sequence[F], word: Sequence[int],
              root: Sequence[F] | None = None) -> F:
    prefix, total = 0, F(0)
    for d in word:
        total += profile(mu, prefix, defects[d], root)
        prefix = (prefix+d) % len(mu)
    return total


def exhaustive_singletons() -> dict[str, int]:
    n, h = 4, 3
    relations = [(a, b, c, (a+b-c) % n)
                 for a, b, c in itertools.product(range(n), repeat=3)]
    total = violations = certified = 0
    for phi in itertools.product(range(h), repeat=n):
        counts = [[sum((phi[(r+d) % n]-phi[r]-label) % h != 0
                       for r in range(n)) for label in range(h)]
                  for d in range(n)]
        for psi in itertools.product(range(h), repeat=n):
            err = [counts[d][psi[d]] for d in range(n)]
            for a, b, c, d in relations:
                total += 1
                cost_numerator = err[a]+err[b]+err[c]+err[d]
                respected = (psi[a]+psi[b]-psi[c]-psi[d]) % h == 0
                if not respected:
                    violations += 1
                    assert cost_numerator >= n, (phi, psi, (a,b,c,d))
                if cost_numerator < n:
                    certified += 1
                    assert respected
    return {"source_modulus": n, "target_modulus": h,
            "function_pairs": h**(2*n), "relations_checked": total,
            "violations_checked": violations, "strict_certificates": certified}


def randomized_fibers() -> dict[str, int]:
    rng = random.Random(SEED)
    relation_count = violation_count = certificates = 0
    dual_count = nested_count = modal_count = 0
    for case in range(220):
        structured = case >= 140
        n = rng.randrange(11, 24) if structured else rng.randrange(2, 10)
        h = n if structured else rng.randrange(2, 8)
        if structured:
            fibers = [[g for _ in range(rng.randrange(1,4))] for g in range(n)]
            if case % 3:
                g = rng.randrange(n)
                fibers[g][0] = (fibers[g][0]+1) % h
            support = set(range(n))
            if case % 7 == 0:
                support.remove(rng.randrange(n))
        else:
            fibers = [[rng.randrange(h) for _ in range(rng.randrange(4))]
                      for _ in range(n)]
            nonempty = [g for g in range(n) if fibers[g]]
            if not nonempty:
                fibers[0] = [0]
                nonempty = [0]
            support = {g for g in nonempty if rng.randrange(4)} or {nonempty[0]}
        labels = (modal_labels(fibers, support, h) if case % 2 or structured
                  else [rng.randrange(h) for _ in range(n)])
        mu, defects, boundary = local_data(fibers, support, labels, h)
        raw = [rng.randrange(1, 8) if g in support else 0 for g in range(n)]
        root = [F(x, sum(raw)) for x in raw]
        for shift in range(n):
            for t in (F(0), F(1,7), F(1,2), F(1)):
                for nu in (mu, root):
                    p = profile(mu, shift, t, nu)
                    assert p == dual_profile(mu, shift, t, nu)
                    dual_count += 1
                c = max(mu[(g-shift) % n]/mu[g] for g in support)
                a = sum(max(F(0), mu[(g-shift) % n]-mu[g]) for g in support)
                mass = sum(mu[(g-shift) % n] for g in support)
                assert profile(mu, shift, t) <= min(c*t, t+a, mass)
        size = sum(len(fibers[g]) for g in support)
        for d in range(n):
            # Verify nested-to-average conversion, including vacuous empty targets.
            for theta in (F(0), F(1,10), F(1,4), F(1,2), F(3,4), F(1)):
                good_sources = 0
                for g in support:
                    target = (g+d) % n
                    for x in fibers[g]:
                        good_targets = sum((y-x-labels[d]) % h == 0
                                           for y in fibers[target])
                        if good_targets >= (1-theta)*len(fibers[target]):
                            good_sources += 1
                if good_sources >= (1-theta)*size:
                    envelope = 1-(1-theta)*max(F(0), 1-theta-boundary[d])
                    assert defects[d] <= envelope
                    assert defects[d] <= 2*theta-theta*theta+boundary[d]
                    nested_count += 1
            # Verify the collision-to-mode bound for the normalized kernel.
            mass = [F(0) for _ in range(h)]
            for g in support:
                target = (g+d) % n
                if target in support:
                    unit = F(1, size*len(fibers[target]))
                    for x in fibers[g]:
                        for y in fibers[target]:
                            mass[(y-x) % h] += unit
            s = sum(mass)
            assert s == 1-boundary[d]
            if s:
                collision = sum((p/s)**2 for p in mass)
                assert max(mass) >= s*collision
                modal_count += 1
        for _ in range(55):
            m, ell = rng.randrange(1,6), rng.randrange(1,6)
            u = [rng.randrange(n) for _ in range(m)]
            v = [rng.randrange(n) for _ in range(ell-1)]
            v.append((sum(u)-sum(v)) % n)
            assert (sum(u)-sum(v)) % n == 0
            respected = (sum(labels[d] for d in u)-sum(labels[d] for d in v)) % h == 0
            for nu in (mu, root):
                cost = word_cost(mu, defects, u, nu)+word_cost(mu, defects, v, nu)
                relation_count += 1
                if not respected:
                    violation_count += 1
                    assert cost >= 1, (case, u, v, str(cost))
                if cost < 1:
                    certificates += 1
                    assert respected
    return {"seed": SEED, "instances": 220,
            "relation_root_pairs_checked": relation_count,
            "violations_checked": violation_count,
            "strict_certificates": certificates,
            "primal_dual_equalities_checked": dual_count,
            "nested_conversions_checked": nested_count,
            "collision_bounds_checked": modal_count}


def sharp_examples() -> dict[str, int]:
    checked = 0
    for k in range(2,21):
        for m in range(2,6):
            n = 2*k*m
            phi = [r//m for r in range(n)]
            for d, label in ((m, 1), (n-m, n-1)):
                bad = sum((phi[(r+d) % n]-phi[r]-label) % n != 0
                          for r in range(n))
                assert F(bad,n) == F(1,2*k)
            assert (k*m-k*(-m)) % n == 0
            assert (k-k*(-1)) % n != 0
            checked += 1
    return {"examples_checked": checked, "k_min": 2, "k_max": 20,
            "m_min": 2, "m_max": 5}


def parameters() -> dict[str, object]:
    eta_old, theta_old = F(1,360**5), F(1,36)
    q_old = 2*theta_old-theta_old**2
    minimal_five = 18*(q_old+eta_old)
    full_nine = (18+72*eta_old)*(q_old+eta_old)
    assert minimal_five < 1 and full_nine < 1
    eta_120, theta_120 = F(1,120**5), F(1,12)
    relaxed_minimal_two = 6*(2*theta_120-theta_120**2+eta_120)
    assert relaxed_minimal_two < 1
    eta_new, theta_new = F(1,75**5), F(2,15)
    relaxed_two = (4+2*eta_new)*(2*theta_new-theta_new**2+eta_new)
    assert relaxed_two < 1
    for k in range(2,1001):
        eta, theta = F(1,(40*k)**5), F(1,4*k)
        bound = (2*k+eta*k*(k-1))*(2*theta-theta**2+eta)
        assert bound < 1
    mu = [F(1,3),F(2,3)]
    assert profile(mu,1,F(1,2)) == F(3,4)
    return {"old_eta": str(eta_old), "relaxed_eta": str(eta_new),
            "allowance_ratio": str((F(360,75))**5),
            "allowance_ratio_decimal": float((F(360,75))**5),
            "minimal_order_five_budget": str(minimal_five),
            "full_order_nine_budget": str(full_nine),
            "relaxed_order_two_budget": str(relaxed_two),
            "minimal_relaxed_eta": str(eta_120),
            "minimal_relaxed_order_two_budget": str(relaxed_minimal_two),
            "general_order_endpoint_checks": 999,
            "general_order_k_range": [2,1000]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    report = {
        "status": "all checks passed",
        "arithmetic": "exact integers and fractions.Fraction; floats only in display",
        "qualification": "Finite computational checks, not a general or Lean proof.",
        "exhaustive_singletons": exhaustive_singletons(),
        "randomized_fibers": randomized_fibers(),
        "sharp_examples": sharp_examples(),
        "parameters": parameters(),
    }
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
