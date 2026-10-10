"""Outward-rounded enclosures for the marginal quartic Bose sum.

This module uses python-flint/Arb for *all* numerical operations.  It combines
rounding enclosures with the analytic contour remainder proved in the article.
Inputs should be decimal/rational strings (not rounded binary floats).

The automatic evaluator applies for every positive s.  It switches between
the convergent Mellin series and positive Bessel terms with a signed
Gaussian-moment/Hurwitz-zeta tail.  Every accuracy-targeted call verifies
the final ball radius, including special-function rounding.  No claim about
the bit complexity of Arb's special-function implementation is made.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from time import perf_counter

from flint import arb, ctx


@dataclass
class Enclosure:
    ball: arb
    analytic_error: arb
    terms: int
    dps: int
    method: str

    def as_dict(self) -> dict:
        return {
            "ball": self.ball.str(self.dps, more=True),
            "total_radius_upper": self.ball.rad().upper().str(self.dps, more=True),
            "analytic_error_upper": self.analytic_error.str(self.dps, more=True),
            "terms": self.terms,
            "working_decimal_precision": self.dps,
            "method": self.method,
            "rounding_included": True,
        }


def _cos_quarter(k: int) -> arb:
    """Exact algebraic values of cos(pi*k/4), with an Arb enclosure."""
    v = arb(2).sqrt() / 2
    return (arb(1), v, arb(0), -v, arb(-1), -v, arb(0), v)[k % 8]


def contour_error(s: arb, j: int) -> arb:
    """Outward-rounded block remainder for degree 4*j+1, j >= 1."""
    if j < 1:
        raise ValueError("The contour block index must be at least one.")
    pi = arb.pi()
    ratio = s / (8 * pi).sqrt()
    bound = (
        pi.sqrt()
        * arb(2 * j + 1).zeta()
        * ratio ** (4 * j + 2)
        / ((4 * j + 2) * (arb(2 * j) + arb(1) / 4) ** (arb(1) / 4))
    )
    return bound.upper()


def mellin_enclosure(
    stiffness: str,
    atol: str = "1e-30",
    dps: int = 80,
    max_degree: int = 20000,
) -> Enclosure:
    """Enclose G(s), including analytic truncation and arithmetic rounding.

    ``atol`` bounds the radius of the returned ball, not relative error.
    A ValueError is raised when the requested accuracy cannot be certified
    at the supplied working precision or degree budget.
    """
    with ctx.workdps(dps):
        s, tolerance = arb(stiffness), arb(atol)
        radius = (8 * arb.pi()).sqrt()
        if not s > 0 or not s < radius:
            raise ValueError("Require a certified 0 < stiffness < sqrt(8*pi).")
        if not tolerance > 0:
            raise ValueError("The absolute tolerance must be positive.")
        j = 1
        bound = contour_error(s, j)
        while not bound < tolerance / 4:
            j += 1
            if 4 * j + 1 > max_degree:
                raise ValueError("Degree budget exhausted near the convergence circle.")
            bound = contour_error(s, j)
        degree = 4 * j + 1
        if degree > max_degree:
            raise ValueError("Degree budget must allow at least five powers.")

        pi = arb.pi()
        quarter, half = arb(1) / 4, arb(1) / 2
        gamma_quarter = quarter.gamma()
        value = gamma_quarter * (-s.log() + pi / 4 + 3 * arb(2).log() / 2)
        value -= (arb(3) / 4).gamma() * half.zeta() * s / 2
        value -= gamma_quarter * s * s / 32
        ratio = s / radius
        power = ratio * ratio
        for k in range(3, degree + 1):
            power *= ratio
            cosine = _cos_quarter(k)
            if cosine.is_zero():
                continue
            a = arb(k) / 2
            coefficient = (
                2 * pi.sqrt() * ((-1) ** k) * cosine
                * (a + quarter).gamma() / (a + half).gamma()
                * a.zeta() / k
            )
            value += coefficient * power
        enclosed = value + arb(0, bound)
        if not enclosed.is_finite() or not enclosed.rad() < tolerance:
            raise ValueError("Increase dps: total rounding radius exceeds atol.")
        return Enclosure(enclosed, bound, degree, dps, "Mellin contour + Arb")


def positive_sum_enclosure(
    stiffness: str,
    direct_terms: int = 512,
    tail_terms: int = 32,
    dps: int = 80,
) -> Enclosure:
    """Independent Bessel sum plus a signed, rigorous Hurwitz-zeta tail.

    The tail bound is valid for every positive s and any N,K >= 1.
    It is useful when N*s**2 is large enough.  It does not use the Mellin
    coefficient series.  The enclosure can be wide if the parameters are
    unsuitable; its width is always reported honestly.
    """
    if direct_terms < 1 or tail_terms < 1:
        raise ValueError("Term counts must be positive integers.")
    with ctx.workdps(dps):
        s = arb(stiffness)
        if not s > 0:
            raise ValueError("stiffness must be positive")
        quarter, half = arb(1) / 4, arb(1) / 2
        total = arb(0)
        for n in range(1, direct_terms + 1):
            u = s * arb(n).sqrt()
            argument = u * u / 8
            psi = u.sqrt() * argument.bessel_k(quarter, scaled=True) / 2
            total += psi / n

        def tail_coefficient(k: int) -> arb:
            return (
                (arb(2 * k) + half).gamma() / arb.fac_ui(k)
                * (arb(k) + arb(5) / 4).zeta(direct_terms + 1)
                / (s ** (arb(2 * k) + half))
            )

        for k in range(tail_terms):
            total += ((-1) ** k) * tail_coefficient(k)
        bound = tail_coefficient(tail_terms).upper()
        # The signed Taylor remainder lies between 0 and (-1)^K * bound.
        signed_center = ((-1) ** tail_terms) * bound / 2
        total += signed_center + arb(0, bound / 2)
        return Enclosure(total, bound, direct_terms + tail_terms, dps,
                         "positive Bessel sum + signed Hurwitz tail + Arb")


def _upper_ceil(value: arb) -> int:
    """Ceiling of a rigorous upper endpoint, used only to allocate work."""
    return int(value.upper().ceil().unique_fmpz())


def accelerated_enclosure(
    stiffness: str | arb,
    atol: str | arb = "1e-30",
    dps: int = 90,
) -> Enclosure:
    """Certified positive-sum evaluator, with an enforced total radius.

    The explicit allocation is uniform-cost only when s >= sqrt(8*pi)/2.
    Using this directly for a very small s is deliberately not efficient;
    ``evaluate`` selects the Mellin representation in that regime.
    """
    with ctx.workdps(dps):
        s, tolerance = arb(stiffness), arb(atol)
        if not s > 0 or not tolerance > 0:
            raise ValueError("stiffness and tolerance must be positive")
        m = max(1, _upper_ceil((4 * arb.pi().sqrt() / tolerance).log()
                               / arb(2).log()))
        n = max(1, _upper_ceil(4 * m / (s * s)))
        result = positive_sum_enclosure(s, n, m, dps)
        if not result.ball.is_finite() or not result.ball.rad() < tolerance:
            raise ValueError("Increase dps: total Bessel/tail radius exceeds atol.")
        return result


def evaluate(
    stiffness: str | arb,
    atol: str | arb = "1e-30",
    dps: int = 90,
) -> Enclosure:
    """Enclose G(s) for any positive s; never return an unchecked width."""
    with ctx.workdps(dps):
        s = arb(stiffness)
        if not s > 0:
            raise ValueError("stiffness must be certified positive")
        if s <= (8 * arb.pi()).sqrt() / 2:
            return mellin_enclosure(s, atol, dps)
        return accelerated_enclosure(s, atol, dps)


def critical_temperature_enclosure(
    temperature_estimate: str,
    stiffness: str,
    density: str,
    density_relative_tolerance: str = "1e-30",
    dps: int = 100,
) -> dict:
    """Certify the continuum root from one density evaluation.

    The supplied temperature need only be positive; a closer guess gives
    a narrower root interval. The root conversion follows from the proved
    bound 1 < d log N / d log T < 5/4. The requested tolerance controls
    density evaluation, not the distance of the input guess from the root.
    """
    with ctx.workdps(dps):
        t, delta, rho = map(arb, (temperature_estimate, stiffness, density))
        target = arb(density_relative_tolerance)
        if not t > 0 or not delta > 0 or not rho > 0 or not target > 0:
            raise ValueError("All physical inputs and tolerances must be positive")
        constant = (arb(1) / 4).gamma() / (16 * arb.pi() ** (arb(5) / 2))
        g = evaluate(delta / t.sqrt(), target * rho / (16 * constant * t), dps)
        ratio = constant * t * g.ball / rho
        if not ratio > 0:
            raise ValueError("Density ratio could not be certified positive")
        lo, hi = ratio.lower(), ratio.upper()
        exponent = -arb(4) / 5
        root = t * ((1 / hi).union(hi ** exponent)
                    .union(1 / lo).union(lo ** exponent))
        return {
            "temperature_ball": root.str(dps, more=True),
            "temperature_radius_upper": root.rad().upper().str(dps, more=True),
            "density_ratio_ball": ratio.str(dps, more=True),
            "temperature_estimate": temperature_estimate,
            "stiffness": stiffness,
            "density": density,
            "rounding_included": True,
            "method": "one Arb density enclosure + global elasticity bounds",
            "g_enclosure": g.as_dict(),
        }


def validation_report() -> dict:
    rows = []
    for s in ("1e-100", "1e-12", "1e-6", "0.001", "0.1", "1", "3", "4.9"):
        start = perf_counter()
        result = mellin_enclosure(s, atol="1e-30", dps=90)
        row = {"stiffness": s, **result.as_dict(),
               "elapsed_seconds": perf_counter() - start}
        if arb(s) >= 1:
            alternate = accelerated_enclosure(s, atol="1e-35", dps=110)
            row["independent_enclosure"] = alternate.as_dict()
            row["independent_overlap"] = result.ball.overlaps(alternate.ball)
            row["independent_radius_below_1e_minus_35"] = bool(
                alternate.ball.rad() < arb("1e-35"))
            if not row["independent_overlap"]:
                raise AssertionError("Independent certified enclosures do not overlap")
            if not row["independent_radius_below_1e_minus_35"]:
                raise AssertionError("Independent enclosure is too wide to validate")
        rows.append(row)
    global_rows = []
    for s in ("2.5", "2.51", "5", "10", "100", "1e100"):
        result = evaluate(s, atol="1e-30", dps=110)
        global_rows.append({"stiffness": s, **result.as_dict()})
    temperature = critical_temperature_enclosure(
        "0.359500750128335309891857687832384873520295167", "0.01", "0.1",
        density_relative_tolerance="1e-45", dps=120)
    return {"description": "Arb enclosures include numerical rounding and analytic tails.",
            "independent_validation_requires_overlap_and_small_radius": True,
            "rows": rows, "global_evaluator_rows": global_rows,
            "critical_temperature_certificate": temperature}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stiffness", nargs="?", default="0.1")
    parser.add_argument("--atol", default="1e-30")
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--validation", type=Path)
    args = parser.parse_args()
    if args.validation:
        report = validation_report()
        args.validation.parent.mkdir(parents=True, exist_ok=True)
        args.validation.write_text(json.dumps(report, indent=2) + "\n")
        print("Wrote certified validation:", args.validation)
    else:
        result = evaluate(args.stiffness, args.atol, args.dps)
        print(json.dumps(result.as_dict(), indent=2))


if __name__ == "__main__":
    main()
