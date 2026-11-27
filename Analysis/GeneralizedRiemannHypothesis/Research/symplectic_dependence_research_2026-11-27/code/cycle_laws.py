#!/usr/bin/env python3
"""Exact symplectic cycle laws, using rational arithmetic only.

Model
-----
Choose independent uniform NONZERO vectors X_1,...,X_ell in a
2*n-dimensional symplectic vector space over F_q.  Write N=q**(2*n), and
observe Y_i=<X_i,X_{i+1}> with indices taken cyclically.  The comparison
law consists of independent edge labels with the SAME one-edge law:

    p(0) = (N-q)/(q*(N-1))
    p(a) = N/(q*(N-1)) for each a != 0.

The complete likelihood is determined by the number z of zero labels
when ell is odd.  When ell=2*k is even, add the following resonance bit
if z=0:

    a_1*a_3*...*a_(2*k-1) = (-1)**k * a_2*a_4*...*a_(2*k).

These are labels in CYCLIC edge orientation.  If an edge is oriented in
the opposite direction, negate its recorded label before applying the
resonance condition.  In characteristic two, negation does nothing.

No field-arithmetic dependency is needed because the multiplicities of
these sufficient-statistic outcomes depend only on q.  All results are
exact fractions; q must be a prime power, n>=1, and ell>=3.

Examples
--------
    python3 cycle_laws.py --q 2 --n 3 --length 3
    python3 cycle_laws.py --q 4 --n 2 --length 6 --format text
    python3 cycle_laws.py --self-check

The built-in checks compare grouped pointwise probabilities with the
separately implemented closed TV and chi-square formulas.  They are
arithmetic consistency checks, not a machine-checked mathematical proof.
The accompanying independent vector enumeration is a separate check.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, isqrt
import json
from typing import Any


def is_prime_power(q: int) -> bool:
    """Return whether q is p**e for a prime p and integer e>=1."""
    if not isinstance(q, int) or isinstance(q, bool) or q < 2:
        return False
    if q % 2 == 0:
        p = 2
    else:
        p = None
        for candidate in range(3, isqrt(q) + 1, 2):
            if q % candidate == 0:
                p = candidate
                break
        if p is None:
            return True
    remaining = q
    while remaining % p == 0:
        remaining //= p
    return remaining == 1


def _validate(q: int, n: int, ell: int | None = None) -> int:
    if not is_prime_power(q):
        raise ValueError("q must be a prime power at least 2")
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError("n must be an integer at least 1")
    if ell is not None and (
        not isinstance(ell, int) or isinstance(ell, bool) or ell < 3
    ):
        raise ValueError("cycle length must be an integer at least 3")
    return q ** (2 * n)


def edge_marginal(q: int, n: int) -> tuple[Fraction, Fraction]:
    """Return (probability of zero, probability of EACH nonzero label)."""
    N = _validate(q, n)
    return Fraction(N - q, q * (N - 1)), Fraction(N, q * (N - 1))


@dataclass(frozen=True)
class CycleGroup:
    """One outcome of an exactly sufficient statistic.

    multiplicity is the number of full edge-label vectors in this group.
    point_probability and independent_point_probability are the mass of
    EACH such vector; group probabilities multiply them by multiplicity.
    likelihood_ratio is constant on the whole group.
    """

    name: str
    zeros: int
    resonance: bool | None
    multiplicity: int
    independent_point_probability: Fraction
    point_probability: Fraction
    independent_group_probability: Fraction
    group_probability: Fraction
    likelihood_ratio: Fraction


def cycle_groups(q: int, n: int, ell: int) -> list[CycleGroup]:
    """Return the exact grouped law, omitting impossible empty groups."""
    N = _validate(q, n, ell)
    p0, p1 = edge_marginal(q, n)
    groups: list[CycleGroup] = []

    def append_group(z: int, resonance: bool | None, multiplicity: int,
                     difference: Fraction) -> None:
        if multiplicity == 0:
            return
        independent = p0 ** z * p1 ** (ell - z)
        actual = independent + difference
        suffix = ""
        if resonance is not None:
            suffix = ", resonant" if resonance else ", nonresonant"
        groups.append(CycleGroup(
            name=f"z={z}{suffix}",
            zeros=z,
            resonance=resonance,
            multiplicity=multiplicity,
            independent_point_probability=independent,
            point_probability=actual,
            independent_group_probability=multiplicity * independent,
            group_probability=multiplicity * actual,
            likelihood_ratio=actual / independent,
        ))

    if ell % 2:
        k = (ell - 1) // 2
        factor = Fraction(N ** (k + 1), q ** ell * (N - 1) ** ell)
        for z in range(ell + 1):
            kappa_product = (q - 1) ** z * (-1) ** (ell - z)
            multiplicity = comb(ell, z) * (q - 1) ** (ell - z)
            append_group(z, None, multiplicity, factor * kappa_product)
    else:
        k = ell // 2
        factor = Fraction(N ** k, q ** ell * (N - 1) ** ell)
        # No zero labels: the multiplicative-resonance distinction matters.
        for resonance in (True, False):
            multiplicity = (q - 1) ** (ell - 1)
            if not resonance:
                multiplicity *= q - 2
            K = Fraction(1 + q ** k * ((q - 1) * int(resonance) - 1), q - 1)
            append_group(0, resonance, multiplicity,
                         factor * ((N - 1) * K - 1))
        # At least one zero label: only the number of zeros matters.
        for z in range(1, ell + 1):
            kappa_product = (q - 1) ** z * (-1) ** (ell - z)
            K = Fraction(kappa_product, q - 1)
            multiplicity = comb(ell, z) * (q - 1) ** (ell - z)
            append_group(z, None, multiplicity,
                         factor * ((N - 1) * K - kappa_product))
    return groups


def cycle_tv(q: int, n: int, ell: int) -> Fraction:
    """Closed formula for TV(actual cycle, independent true marginals)."""
    N = _validate(q, n, ell)
    if ell % 2:
        return Fraction(
            2 ** (ell - 1) * (q - 1) ** ell * N ** ((ell + 1) // 2),
            q ** ell * (N - 1) ** ell,
        )
    k = ell // 2
    bracket = ((N - q) * ((q - 1) * 2 ** (ell - 1) - (q - 2))
               + (N - 1) * (q - 2) * q ** k)
    return Fraction(N ** k * (q - 1) ** (ell - 2) * bracket,
                    q ** ell * (N - 1) ** ell)


def cycle_chi_square(q: int, n: int, ell: int) -> Fraction:
    """Closed formula for chi-square(actual cycle || independent edges)."""
    N = _validate(q, n, ell)
    if ell % 2:
        return Fraction((q - 1) ** ell * N, (N - q) ** ell)
    return (q - 1) ** (ell - 2) * (
        Fraction(1, (N - q) ** (ell - 2))
        + Fraction(q - 2, (N - 1) ** (ell - 2))
    )


def cactus_chi_square(q: int, n: int, cycle_counts: dict[int, int]) -> Fraction:
    """Exact chi-square divergence for a cactus with given cycle counts.

    Bridges contribute zero divergence and need not be specified.  This
    is valid because whole cycle blocks (and bridges) are independent.
    """
    _validate(q, n)
    product = Fraction(1)
    for ell, count in sorted(cycle_counts.items()):
        _validate(q, n, ell)
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            raise ValueError("cycle counts must be nonnegative integers")
        product *= (1 + cycle_chi_square(q, n, ell)) ** count
    return product - 1


def verify_law(q: int, n: int, ell: int) -> dict[str, Any]:
    """Check normalization, positivity, and grouped-vs-closed divergences."""
    groups = cycle_groups(q, n, ell)
    assert sum(group.multiplicity for group in groups) == q ** ell
    assert sum((group.group_probability for group in groups), Fraction()) == 1
    assert sum((group.independent_group_probability for group in groups),
               Fraction()) == 1
    assert all(0 <= group.point_probability <= 1 for group in groups)
    assert all(0 < group.independent_point_probability <= 1 for group in groups)
    grouped_tv = sum((abs(group.group_probability
                          - group.independent_group_probability)
                      for group in groups), Fraction()) / 2
    grouped_chi = sum((group.independent_group_probability
                       * (group.likelihood_ratio - 1) ** 2
                       for group in groups), Fraction())
    assert grouped_tv == cycle_tv(q, n, ell)
    assert grouped_chi == cycle_chi_square(q, n, ell)
    assert 0 < grouped_tv < 1
    assert grouped_chi > 0
    return {
        "q": q, "n": n, "length": ell, "groups": len(groups),
        "point_vectors": q ** ell, "status": "passed",
    }


def self_check() -> dict[str, Any]:
    """Run deterministic exact checks across fields, dimensions and lengths."""
    checks = []
    for q in (2, 3, 4, 5, 7, 8, 9, 16, 25):
        for n in (1, 2, 3, 6):
            for ell in range(3, 15):
                checks.append(verify_law(q, n, ell))
    for invalid in (0, 1, 6, 10, 12, 15, 18):
        assert not is_prime_power(invalid)
    return {
        "status": "passed",
        "exact_parameter_cases": len(checks),
        "checks": ["normalization", "nonnegativity", "group multiplicities",
                   "TV grouped sum versus closed formula",
                   "chi-square grouped sum versus closed formula",
                   "prime-power validation"],
        "q_values": [2, 3, 4, 5, 7, 8, 9, 16, 25],
        "n_values": [1, 2, 3, 6],
        "length_range": [3, 14],
        "scope": "Exact arithmetic consistency; separate from vector enumeration.",
    }


def decimal_string(value: Fraction, digits: int = 18) -> str:
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def _json_ready(value: Any) -> Any:
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {str(key): _json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_ready(item) for item in value]
    return value


def result_record(q: int, n: int, ell: int) -> dict[str, Any]:
    """Return a JSON-serializable exact law plus useful decimal summaries."""
    N = _validate(q, n, ell)
    validation = verify_law(q, n, ell)
    p0, p1 = edge_marginal(q, n)
    tv = cycle_tv(q, n, ell)
    chi = cycle_chi_square(q, n, ell)
    r = (ell - 1) // 2
    return _json_ready({
        "model": "symplectic pairings of independent uniform nonzero vectors",
        "comparison": "independent edges with the same one-edge marginals",
        "q": q,
        "n": n,
        "ambient_dimension": 2 * n,
        "N": N,
        "length": ell,
        "edge_probability_zero": p0,
        "edge_probability_each_nonzero": p1,
        "tv": tv,
        "tv_decimal": decimal_string(tv),
        "chi_square": chi,
        "chi_square_decimal": decimal_string(chi),
        "asymptotic_r": r,
        "chi_square_leading_constant": (q - 1) ** (2 * r + 1),
        "chi_square_leading_power_of_N": -2 * r,
        "groups": [asdict(group) for group in cycle_groups(q, n, ell)],
        "orientation": "cyclic; negate reverse-oriented edge labels first",
        "validation": validation,
    })


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--q", type=int, default=2, help="field order (prime power)")
    parser.add_argument("--n", type=int, default=1,
                        help="half the ambient symplectic dimension")
    parser.add_argument("--length", "--ell", dest="ell", type=int, default=3,
                        help="cycle length, at least 3")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--self-check", action="store_true",
                        help="run exact arithmetic consistency checks")
    args = parser.parse_args()
    try:
        if args.self_check:
            record = self_check()
            print(json.dumps(record, indent=2))
            return
        record = result_record(args.q, args.n, args.ell)
    except ValueError as error:
        parser.error(str(error))
    if args.format == "json":
        print(json.dumps(record, indent=2))
        return
    print(f"Symplectic cycle: q={args.q}, dimension={2 * args.n}, length={args.ell}")
    print(f"N = {record['N']}")
    print(f"p(0) = {record['edge_probability_zero']}")
    print(f"p(each nonzero) = {record['edge_probability_each_nonzero']}")
    print(f"TV = {record['tv']}  ({record['tv_decimal']})")
    print(f"chi-square = {record['chi_square']}  ({record['chi_square_decimal']})")
    print("Exactly sufficient groups:")
    for group in record["groups"]:
        print(f"  {group['name']}: multiplicity={group['multiplicity']}; "
              f"actual mass={group['group_probability']}; "
              f"independent mass={group['independent_group_probability']}; "
              f"likelihood={group['likelihood_ratio']}")
    print("Exact arithmetic consistency checks passed.")


if __name__ == "__main__":
    main()
