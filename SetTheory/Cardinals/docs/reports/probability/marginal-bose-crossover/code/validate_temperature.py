"""Independently recompute the certified example at 115 mpmath digits."""

from pathlib import Path
import json

from mpmath import mp
from flint import arb, ctx

from bose_crossover import critical_temperature, critical_density


def main():
    root = Path(__file__).resolve().parents[1]
    certificate = json.loads((root / "data/certified_validation.json").read_text())
    temperature_ball = certificate["critical_temperature_certificate"]["temperature_ball"]
    mp.dps = 115
    rho, delta, tolerance = mp.mpf('.1'), mp.mpf('.01'), mp.mpf('1e-90')
    t = critical_temperature(rho, delta, relative_tol=tolerance)
    residual = abs(critical_density(t, delta, abs_tol=mp.mpf('1e-100')) / rho - 1)
    digits = mp.nstr(t, 110)
    with ctx.workdps(140):
        ball, numerical = arb(temperature_ball), arb(digits)
        contains = bool(ball.contains(numerical))
        distance = abs(ball.mid() - numerical).str(35, more=True)
    if not contains:
        raise AssertionError("The independent numerical root is outside the Arb interval")
    report = {
        "rho": ".1", "delta": ".01", "working_decimal_precision": 115,
        "relative_tolerance": "1e-90", "temperature_mpmath": digits,
        "density_relative_residual": mp.nstr(residual, 35),
        "rounding_certified": False,
        "purpose": "Independent higher-precision numerical root for comparison with the Arb density-to-temperature enclosure.",
        "arb_ball_contains_highprecision_numerical_value": contains,
        "numerical_distance_from_certificate_midpoint": distance,
        "certificate_temperature_ball": temperature_ball,
    }
    target = root / "data/critical_temperature_crosscheck.json"
    target.write_text(json.dumps(report, indent=2)+"\n")
    print("Independent 115-digit numerical root lies inside the Arb certificate.")
    print("Density relative residual:", mp.nstr(residual, 12))


if __name__ == "__main__":
    main()
