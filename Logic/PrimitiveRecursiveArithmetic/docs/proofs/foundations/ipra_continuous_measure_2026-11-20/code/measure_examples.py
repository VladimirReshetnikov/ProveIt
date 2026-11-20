#!/usr/bin/env python3
"""Exact finite examples for the measure chapter.

All arithmetic uses fractions.Fraction.  The checks below validate the
implemented finite operations and the explicitly displayed examples.  They
are not universal proofs, do not verify primitive-recursiveness inside iPRA,
and are not a substitute for the Lean or object-theory obligations.

Run from any directory.  The result is saved to validation/measure_examples.json
next to this package's code directory, and a concise summary is printed.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json


@dataclass(frozen=True)
class Simple:
    level: int
    values: tuple[Q, ...]


class DyadicTower:
    """A fixed rational Bernoulli bias; p=0 includes zero-mass cells."""

    def __init__(self, p: Q = Q(1, 2)) -> None:
        assert 0 <= p <= 1
        self.p = p

    def size(self, n: int) -> int:
        return 1 << n

    def weights(self, n: int) -> tuple[Q, ...]:
        return tuple(
            self.p ** i.bit_count() * (1 - self.p) ** (n - i.bit_count())
            for i in range(1 << n)
        )

    def project(self, m: int, n: int, i: int) -> int:
        assert 0 <= m <= n and 0 <= i < self.size(n)
        return i >> (n - m)


class AnnulusTower:
    """A_j have mass 4^(-j-1); the last atom is the unsplit remainder.

    One interval realization is A_j=[2^(-2j-2),2^(-2j-1)).  At level n,
    the first n annuli are exposed.  The remainder includes all later annuli
    and the complement of their union.  This sparse presentation has n+1
    cells rather than the 4^n cells of an equally fine dyadic grid.
    """

    def size(self, n: int) -> int:
        return n + 1

    def weights(self, n: int) -> tuple[Q, ...]:
        first = tuple(Q(1, 4 ** (j + 1)) for j in range(n))
        return first + (1 - sum(first, Q(0)),)

    def project(self, m: int, n: int, i: int) -> int:
        assert 0 <= m <= n and 0 <= i <= n
        return min(m, i)


Tower = DyadicTower | AnnulusTower


def simple(tower: Tower, level: int, values) -> Simple:
    result = Simple(level, tuple(Q(v) for v in values))
    assert len(result.values) == tower.size(level)
    return result


def lift(tower: Tower, s: Simple, n: int) -> Simple:
    assert n >= s.level
    return simple(tower, n, (
        s.values[tower.project(s.level, n, i)] for i in range(tower.size(n))
    ))


def common(tower: Tower, s: Simple, t: Simple):
    n = max(s.level, t.level)
    return tower.weights(n), lift(tower, s, n).values, lift(tower, t, n).values


def integral(tower: Tower, s: Simple) -> Q:
    return sum((w * x for w, x in zip(tower.weights(s.level), s.values)), Q(0))


def norm(tower: Tower, s: Simple) -> Q:
    return sum((w * abs(x) for w, x in zip(tower.weights(s.level), s.values)), Q(0))


def distance(tower: Tower, s: Simple, t: Simple) -> Q:
    ws, xs, ys = common(tower, s, t)
    return sum((w * abs(x - y) for w, x, y in zip(ws, xs, ys)), Q(0))


def rho(tower: Tower, s: Simple, t: Simple) -> Q:
    ws, xs, ys = common(tower, s, t)
    return sum((w * min(Q(1), abs(x - y)) for w, x, y in zip(ws, xs, ys)), Q(0))


def tail(tower: Tower, s: Simple, cutoff: Q) -> Q:
    return sum((w * max(Q(0), abs(x) - cutoff)
                for w, x in zip(tower.weights(s.level), s.values)), Q(0))


def conditional(tower: Tower, s: Simple, n: int) -> Simple:
    r = max(s.level, n)
    sr = lift(tower, s, r)
    fine = tower.weights(r)
    coarse = tower.weights(n)
    out = []
    for i, wi in enumerate(coarse):
        numerator = sum((fine[j] * sr.values[j] for j in range(tower.size(r))
                         if tower.project(n, r, j) == i), Q(0))
        if wi == 0:
            assert numerator == 0
            out.append(Q(0))
        else:
            out.append(numerator / wi)
    return simple(tower, n, out)


def validate_tower(tower: Tower, max_level: int) -> int:
    checks = 0
    for n in range(max_level + 1):
        weights = tower.weights(n)
        assert len(weights) == tower.size(n)
        assert all(w >= 0 for w in weights)
        assert sum(weights, Q(0)) == 1
        checks += 1
        for m in range(n + 1):
            for i, wi in enumerate(tower.weights(m)):
                assert sum((weights[j] for j in range(tower.size(n))
                            if tower.project(m, n, j) == i), Q(0)) == wi
                checks += 1
            for ell in range(m + 1):
                for j in range(tower.size(n)):
                    assert tower.project(ell, n, j) == tower.project(
                        ell, m, tower.project(m, n, j))
                    checks += 1
    return checks


def ceil_log2(b: int) -> int:
    assert b >= 1
    # Explicitly bounded search, matching the paper.
    for k in range(b + 1):
        if b <= 1 << k:
            return k
    raise AssertionError("The elementary bound 2^b >= b failed")


def annulus_partial(n: int) -> Simple:
    return simple(AnnulusTower(), n, [2 ** j for j in range(n)] + [0])


def annulus_limit_conditional(n: int) -> Simple:
    # g has value 2^j on A_j and zero on the remaining set.
    # Integral of its unexposed tail: sum_{j>=n} 2^j 4^(-j-1).
    tail_integral = Q(1, 2 ** (n + 1))
    remaining_mass = AnnulusTower().weights(n)[-1]
    return simple(AnnulusTower(), n,
                  [2 ** j for j in range(n)] + [tail_integral / remaining_mass])


def halting_signal(tower: DyadicTower, n: int, first_halt: int | None) -> Simple:
    if first_halt is None or first_halt > n:
        return simple(tower, n, [0] * tower.size(n))
    assert first_halt >= 1
    return simple(tower, n, (
        1 if ((i >> (n - first_halt)) & 1) == 0 else -1
        for i in range(tower.size(n))
    ))


def run() -> dict:
    counts = {"tower_contracts": 0, "scalar_clipping": 0,
              "operator_laws": 0, "vitali_budgets": 0, "martingale_steps": 0}

    for tower in [DyadicTower(), DyadicTower(Q(0)),
                  DyadicTower(Q(1, 1024)), AnnulusTower()]:
        counts["tower_contracts"] += validate_tower(tower, 4)

    values = [Q(-7, 2), Q(-2), Q(-1), Q(-1, 3), Q(0), Q(1, 2), Q(1), Q(2), Q(5)]
    for x, y, k in product(values, values, [Q(1), Q(3, 2), Q(4)]):
        excess_x = max(Q(0), abs(x) - k)
        excess_y = max(Q(0), abs(y) - k)
        assert abs(x - y) <= excess_x + excess_y + 2 * k * min(Q(1), abs(x - y))
        assert abs(excess_x - excess_y) <= abs(x - y)
        counts["scalar_clipping"] += 1

    # Regression for the invalid displayed inequality in the prior packet.
    x, y, k = Q(2), Q(-1), Q(1)
    invalid_rhs = (abs(x - y) if abs(x) <= k and abs(y) <= k else Q(0))
    invalid_rhs += abs(x) if abs(x) > k else Q(0)
    invalid_rhs += abs(y) if abs(y) > k else Q(0)
    correct_rhs = max(Q(0), abs(x) - k) + max(Q(0), abs(y) - k) + 2 * k * min(Q(1), abs(x - y))
    assert abs(x - y) > invalid_rhs
    assert abs(x - y) == correct_rhs

    for tower in [DyadicTower(), DyadicTower(Q(0)), DyadicTower(Q(1, 1024)), AnnulusTower()]:
        for r in range(5):
            s = simple(tower, r, (Q((i * 7) % 13 - 6, i % 3 + 1)
                                 for i in range(tower.size(r))))
            t = simple(tower, r, (Q((i * 3) % 11 - 5, i % 4 + 1)
                                 for i in range(tower.size(r))))
            for n in range(5):
                en_s, en_t = conditional(tower, s, n), conditional(tower, t, n)
                assert integral(tower, en_s) == integral(tower, s)
                assert distance(tower, en_s, en_t) <= distance(tower, s, t)
                assert tail(tower, en_s, Q(2)) <= tail(tower, s, Q(2))
                for m in range(5):
                    lhs = conditional(tower, en_s, m)
                    rhs = conditional(tower, s, min(m, n))
                    assert distance(tower, lhs, rhs) == 0
                    counts["operator_laws"] += 1

    tower = AnnulusTower()
    vitali_rows = []
    for k in range(9):
        cutoff = 2 ** (k + 1)  # U(k+2), U(j)=max(1,2^(j-1))
        q = k + 2 + ceil_log2(2 * cutoff)
        N = q                 # R(j)=j for g_n
        assert N == 2 * k + 4
        for m, n in product(range(N, N + 4), repeat=2):
            sm, sn = annulus_partial(m), annulus_partial(n)
            target = Q(1, 2 ** k)
            assert tail(tower, sm, Q(cutoff)) <= target / 4
            assert tail(tower, sn, Q(cutoff)) <= target / 4
            assert rho(tower, sm, sn) <= Q(1, 2 ** q)
            budget = tail(tower, sm, Q(cutoff)) + tail(tower, sn, Q(cutoff)) + 2 * cutoff * rho(tower, sm, sn)
            assert distance(tower, sm, sn) <= budget <= 3 * target / 4
            counts["vitali_budgets"] += 1
        actual_error = Q(1, 2 ** (N + 1))
        assert actual_error <= 3 * Q(1, 2 ** k) / 4
        vitali_rows.append({"precision": k, "cutoff_U_k_plus_2": cutoff,
                            "rho_precision": q, "rate_N": N,
                            "certified_L1_error": str(3 * Q(1, 2 ** k) / 4),
                            "actual_L1_error_g_N": str(actual_error)})

    ce_rows = []
    for n in range(9):
        en_g = annulus_limit_conditional(n)
        assert integral(tower, en_g) == Q(1, 2)
        exact_error = Q(2, 2 ** n) / (2 + Q(1, 4 ** n))
        assert exact_error <= Q(1, 2 ** n)
        # Independent finite approximation brackets the infinite norm.
        sm = annulus_partial(n + 12)
        computed = distance(tower, en_g, sm)
        omitted_tail = Q(1, 2 ** (n + 13))
        assert abs(computed - exact_error) <= omitted_tail
        ce_rows.append({"level": n, "atom_count": n + 1,
                        "conditional_value_on_remainder": str(en_g.values[-1]),
                        "exact_L1_error": str(exact_error),
                        "density_bound": str(Q(1, 2 ** n))})

    fair = DyadicTower()
    for first_halt in [None, 1, 2, 3, 4, 5]:
        for n in range(6):
            now = halting_signal(fair, n, first_halt)
            nxt = halting_signal(fair, n + 1, first_halt)
            assert distance(fair, conditional(fair, nxt, n), now) == 0
            assert tail(fair, now, Q(1)) == 0
            if first_halt == n + 1:
                assert distance(fair, now, nxt) == 1
                assert rho(fair, now, nxt) == 1
            counts["martingale_steps"] += 1

    spike_rows = []
    for n in range(1, 9):
        spike = simple(fair, n, [2 ** n] + [0] * ((1 << n) - 1))
        zero = simple(fair, 0, [0])
        assert norm(fair, spike) == 1
        assert rho(fair, spike, zero) == Q(1, 2 ** n)
        assert tail(fair, spike, Q(1)) == 1 - Q(1, 2 ** n)
        spike_rows.append({"n": n, "norm": "1", "rho_to_zero": str(rho(fair, spike, zero)),
                           "excess_above_1": str(tail(fair, spike, Q(1)))})

    return {
        "status": "all exact finite checks passed",
        "scope": "Implementation validation and exact worked examples, not universal proofs or object-iPRA derivations.",
        "check_counts": counts,
        "prior_vitali_counterexample": {"x": "2", "y": "-1", "K": "1",
                                         "left": str(abs(x-y)), "prior_rhs": str(invalid_rhs),
                                         "correct_clipping_rhs": str(correct_rhs)},
        "unbounded_dominator": {"definition": "g=sum_j 2^j 1_Aj, mass(Aj)=4^(-j-1)",
                                "integral": "1/2", "simple_name_error_at_n": "2^(-n-1)",
                                "cutoff_U_k": "max(1,2^(k-1))", "vitali_rows": vitali_rows},
        "conditional_expectation": ce_rows,
        "moving_spikes_without_uniform_integrability": spike_rows,
        "martingale_obstruction": "Finite checks verify the fair-sign jump construction. The halting reduction is proved in the report, not established by these checks."
    }


if __name__ == "__main__":
    result = run()
    destination = Path(__file__).resolve().parents[1] / "validation" / "measure_examples.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    print(json.dumps(result["check_counts"], sort_keys=True))
    print(f"Recorded exact examples in {destination}")
