#!/usr/bin/env python3
"""Exact arithmetic for the proposed tapered-Hermite parameter change.

This module does not implement SAT counting or tensor contraction.  It checks
the local interpolation budget, valuations, and the leading constants in the
written analysis.  Its arithmetic functions use Python integers/Fractions;
floating point is used only to display the asymptotic constants.
"""

from dataclasses import asdict, dataclass
from fractions import Fraction
import json
import math


def ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("positive denominator required")
    return -(-n // d)


def v2(n: int) -> int:
    """The 2-adic valuation of a nonzero integer."""
    if not isinstance(n, int) or n == 0:
        raise ValueError("v2 requires a nonzero integer")
    n = abs(n)
    return (n & -n).bit_length() - 1


def rational_v2(x: Fraction) -> int:
    if x == 0:
        raise ValueError("valuation at zero is not finite")
    return v2(x.numerator) - v2(x.denominator)


@dataclass(frozen=True)
class Taper:
    a: int
    u: int
    M: int
    L: int
    h: int
    degree: int
    multiplicity_per_unit_h: int
    total_multiplicity: int

    def multiplicity(self, valuation: int) -> int:
        return self.h * max(0, self.u - valuation)


def exact_taper(a: int, u: int, M: int) -> Taper:
    """Return the smallest positive integral h meeting the degree budget.

    Grid S={-2^a,...,2^a-1}; node zero is omitted.  At a nonzero
    node t the multiplicity is h max(0,u-v2(t)).  We require 1<=u<=a
    and M>=1.  The construction is valid even when the asymptotic
    contraction schedule's stronger assumptions do not apply.
    """
    if not all(isinstance(z, int) for z in (a, u, M)):
        raise ValueError("integer parameters required")
    if not (a >= 1 and 1 <= u <= a and M >= 1):
        raise ValueError("require a>=1, 1<=u<=a, M>=1")
    L = 1 << a
    degree = M * (2 * L - 1)
    # Equals L (2u - 2 + 2^(1-u)), evaluated without fractions.
    denominator = L * (2 * u - 2) + (1 << (a + 1 - u))
    h = ceil_div(degree + 1, denominator)
    return Taper(a, u, M, L, h, degree, denominator, h * denominator)


def grid(taper: Taper):
    return range(-taper.L, taper.L)


def active_nodes(taper: Taper):
    return [t for t in grid(taper)
            if t != 0 and v2(t) < taper.u]


def hermite_valuation_direct(taper: Taper, t: int) -> int:
    """Evaluate v2(E_t(0)) directly from its product's valuations."""
    if t not in grid(taper) or t == 0 or v2(t) >= taper.u:
        raise ValueError("an active node is required")
    return sum(taper.multiplicity(v2(q)) * (v2(q) - v2(t - q))
               for q in grid(taper) if q not in (0, t))


def hermite_valuation_by_levels(taper: Taper, t: int) -> int:
    """Evaluate the source's exact valuation identity by levels."""
    i = v2(t)
    if t not in grid(taper) or t == 0 or i >= taper.u:
        raise ValueError("an active node is required")
    D = taper.L >> i
    return sum((D >> j) * j
               * (taper.multiplicity(i + j) - taper.multiplicity(i))
               for j in range(1, taper.a - i + 1))


def hermite_multiplier_exact(taper: Taper, t: int) -> Fraction:
    """Construct E_t(0) as a rational number (small cases only)."""
    if t not in active_nodes(taper):
        raise ValueError("an active node is required")
    answer = Fraction(1)
    for q in grid(taper):
        if q in (0, t):
            continue
        multiplicity = taper.multiplicity(v2(q))
        if multiplicity:
            answer *= Fraction(-q, t - q) ** multiplicity
    return answer


def p_child(p: int, taper: Taper, t: int) -> int:
    """A safe precision for the quotient's first q_t coefficients."""
    if not isinstance(p, int) or p < 1:
        raise ValueError("positive integral parent precision required")
    if t not in active_nodes(taper):
        raise ValueError("an active node is required")
    D = taper.L >> v2(t)
    return p + 6 * taper.h * D + taper.h * taper.u * (taper.a + 1) + 1


def retained_error_valuation(p: int, taper: Taper, t: int, j: int) -> int:
    """Valuation of a 2^p_child error after its recovery multiplier.

    An arbitrary coefficient error divisible by 2^p_child has at
    least this valuation after multiplication by E_t(0)(-t/alpha)^j.
    """
    if not (0 <= j < taper.multiplicity(v2(t))):
        raise ValueError("j must index a retained Taylor coefficient")
    return (p_child(p, taper, t) + hermite_valuation_direct(taper, t)
            + j * (v2(t) - taper.a - 1))


def leading_constants() -> dict:
    """Leading coefficients in base-two time upper-bound certificates.

    The old coefficient is an upper bound obtained from the source's
    schedule with the optimized colored-partition estimate.  Neither
    coefficient is a lower bound on the corresponding implementation.
    """
    new_tree = (2 * math.pi * math.sqrt(6 * 720)
                / (math.log(2) * (1 - Fraction(3, 128) * math.sqrt(12))))
    old_tree = (2 * math.pi * math.sqrt(24 * 131072)
                / (math.log(2) * (1 - Fraction(3, 32) * math.sqrt(2))))
    return {
        "revised": new_tree,
        "source_schedule_tree": old_tree,
        "source_schedule_including_original_leaf_cutoff": old_tree + 1,
        "revised_active_u_power": 1 - math.log(12) / math.log(128 / 3),
        "interpretation": "Leading coefficients of proved upper-bound analyses, not measured running times or lower bounds.",
    }


def schedule_algebra() -> dict:
    """Exact exponents implied by r=256, eta=1/720, and decay=12."""
    eta = Fraction(1, 720)
    a_bound = 2 * eta / (1 - Fraction(1, 12))
    gamma = Fraction(9, 10)
    array_exponent = 16 * a_bound
    return {
        "a_over_lambda_upper_bound": str(a_bound),
        "L_exponent_upper_bound": str(a_bound),
        "D_array_exponent_upper_bound": str(array_exponent),
        "degree_times_D_array_squared_exponent": str(gamma + 2 * array_exponent),
        "L_times_D_array_exponent": str(a_bound + array_exponent),
        "child_edge_ratio": str(Fraction(6, 256)),
    }


def schedule_from_log(lam: int) -> dict:
    """Inspect active-depth bounds without materializing s=2^lam.

    Integer comparisons use (128/3)^d < lam, a necessary condition for
    an active call when H=ceil(s/lam).  Checks of packing use the lower
    bound M>s/lam.  For lambda divisible by ten the declared input
    degree bound s^(9/10) is integral.  This is a numerical sanity check,
    not the proof of the eventual asymptotic inequalities.
    """
    if lam < 2 or lam % 10:
        raise ValueError("require lambda>=2 divisible by ten")
    maximum_depth = -1
    lhs, rhs = 1, lam
    while lhs < rhs:
        maximum_depth += 1
        lhs *= 128
        rhs *= 3
    values = [lam // (720 * 12 ** d) for d in range(maximum_depth + 1)]
    a_values = []
    cumulative = 0
    for u in values:
        cumulative += 2 * u
        a_values.append(cumulative)
    ceil_log_lam = (lam - 1).bit_length()
    minimum_log_edges = lam - ceil_log_lam
    packing = all(minimum_log_edges >= 1 + 32 * a + 9 * lam // 10
                  and minimum_log_edges >= 17 * a
                  and 1 + a <= 9 * lam // 10
                  for a in a_values)
    return {
        "lambda": lam,
        "maximum_possible_active_depth": maximum_depth,
        "u_values": values,
        "a_values": a_values,
        "all_u_positive": all(u >= 1 for u in values),
        "packing_inequalities_sufficiently_certified": packing,
        "a_bound_holds": all(Fraction(a, lam) <= Fraction(1, 330)
                              for a in a_values),
    }


if __name__ == "__main__":
    print(json.dumps({"scope": __doc__.strip(),
                      "leading_constants": leading_constants(),
                      "schedule_algebra": schedule_algebra(),
                      "example_taper": asdict(exact_taper(5, 4, 16)),
                      "large_logarithm_sanity_checks":
                          [schedule_from_log(z) for z in (10**12, 10**15, 10**18)]},
                     indent=2))
