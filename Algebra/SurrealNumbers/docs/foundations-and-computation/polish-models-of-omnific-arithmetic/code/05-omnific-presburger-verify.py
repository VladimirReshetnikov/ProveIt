"""Deterministic exact checks supporting polish_presburger_glazer.tex.

These tests verify finite instances and executed prefixes. They do not
replace proofs of induction, Polishness, or arbitrary infinite-stream laws.
Run: python verify.py
"""
from fractions import Fraction as F
from random import Random
import json
import platform
from pathlib import Path

from polish_presburger import (
    FiniteLex as E, add_codes, compare_approx, decode, encode, numeral,
    pair, positive_index, positive_rational, quotient_code,
    rational, rational_index, unpair,
)

rng = Random(231113699)
counts: dict[str, int] = {}


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    counts[name] = counts.get(name, 0) + 1


for a in range(35):
    for b in range(35):
        check("pairing_round_trip", unpair(pair(a, b)) == (a, b))
for i in range(500):
    check("positive_rational_round_trip", positive_index(positive_rational(i)) == i)
    check("signed_rational_round_trip", rational_index(rational(i)) == i)


def random_element(rank: int) -> E:
    return E(tuple(F(rng.randrange(-12, 13), rng.randrange(1, 8))
                   for _ in range(rank)), rng.randrange(-35, 36))


for _ in range(2400):
    rank = rng.randrange(1, 5)
    a, b, c = (random_element(rank) for _ in range(3))
    zero, one = E.constant(rank, 0), E.constant(rank, 1)
    check("additive_group_laws",
          a + b == b + a and (a + b) + c == a + (b + c) and a + (-a) == zero)
    check("order_translation", a.compare(b) == (a + c).compare(b + c))
    if a.positive():
        check("least_positive_one", a.compare(one) >= 0)
    m = rng.randrange(1, 14)
    q, r = a.divmod(m)
    check("division_identity", q.scale(m) + E.constant(rank, r) == a and 0 <= r < m)
    if a.nonnegative():
        check("nonnegative_quotient", q.nonnegative())
    if a.nonnegative() and b.nonnegative():
        check("cone_addition", (a + b).nonnegative())
    # A parameter-dependent conjunction of congruences is coset-invariant.
    modulus = 12
    def predicate(x: E) -> bool:
        return ((x - b).integer % 3 == 0 and
                (x + c).integer % 4 != 1)
    check("coset_invariance", predicate(a) == predicate(a + b.scale(modulus)))
    # Construct a witness in a nonstandard interval; reduce it to a finite candidate.
    lo = b
    gap = a if a.nonnegative() else -a
    witness = lo + gap
    hi = witness + one
    residue = (witness - lo).integer % modulus
    candidate = lo + E.constant(rank, residue)
    check("finite_interval_candidate",
          candidate.compare(lo) >= 0 and candidate.compare(hi) <= 0 and
          predicate(candidate) == predicate(witness))

# Deliberate counterexample to lifting mere standard-shift periodicity.
u = E((F(1),), 0)
m = 7
P = lambda x: x.coefficients[0] > 0
check("weak_periodicity_counterexample",
      P(u) and P(u + E.constant(1, m)) and
      not any(P(E.constant(1, r)) for r in range(m)))

# Arbitrary Baire codes are valid; check exact decoding/encoding on prefixes.
for case in range(100):
    digits = [rng.randrange(0, 36)] + [rng.randrange(0, 15) for _ in range(18)]
    tail = rng.randrange(0, 8)
    code = lambda i, d=digits, t=tail: d[i] if i < len(d) else t
    n, a = decode(code)
    rebuilt = encode(n, a)
    check("baire_codec_prefix_round_trip", all(code(i) == rebuilt(i) for i in range(16)))

# Operations on promised finite-support elements, with exact stream comparison.
for case in range(140):
    def element():
        lead = rng.randrange(0, 6)
        values = [F(0)] * lead + [F(rng.randrange(1, 5), rng.randrange(1, 5))]
        values += [F(rng.randrange(-4, 5), rng.randrange(1, 5)) for _ in range(5)]
        integer = rng.randrange(-8, 9)
        coefficients = lambda i, v=values: v[i] if i < len(v) else F(0)
        return integer, coefficients, encode(integer, coefficients)
    n, a, left = element()
    z, b, right = element()
    result = add_codes(left, right)
    out_n, out_a = decode(result)
    check("baire_addition_prefix", out_n == n + z and
          all(out_a(i) == a(i) + b(i) for i in range(15)))
    qcode, rem = quotient_code(result, 5)
    qn, qa = decode(qcode)
    check("baire_division_prefix", 5 * qn + rem == out_n and
          0 <= rem < 5 and all(5 * qa(i) == out_a(i) for i in range(15)))
    unit_result = add_codes(left, numeral(1))
    unit_n, unit_a = decode(unit_result)
    check("baire_successor_prefix", unit_n == n + 1 and
          all(unit_a(i) == a(i) for i in range(15)))
    approx = [compare_approx(left, right, stage) for stage in range(15)]
    check("comparison_one_mind_change",
          sum(x != y for x, y in zip(approx, approx[1:])) <= 1)

# Topologically small positive infinite elements have visible negative constants
# after predecessor. The metric assertion is supplied by the article's proof.
for k in range(1, 80):
    x = E((F(1, k),), 0)
    pred = x - E.constant(1, 1)
    check("predecessor_boundary_witness", x.positive() and pred.positive() and pred.integer == -1)

report = {
    "seed": 231113699,
    "python_version": platform.python_version(),
    "checks_by_family": counts,
    "total_checks": sum(counts.values()),
    "status": "PASS",
    "scope": "Exact finite instances and finite stream prefixes; not a formal proof.",
}
print(json.dumps(report, indent=2))
Path(__file__).with_name("verification_results.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8")
