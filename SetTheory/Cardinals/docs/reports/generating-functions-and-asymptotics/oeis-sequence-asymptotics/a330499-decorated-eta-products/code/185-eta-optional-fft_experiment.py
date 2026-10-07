#!/usr/bin/env python3
"""Independent FFT extraction of the eta-transformed generating function.

Default finite grid: 262144 points, kappa=40, 80 eta modes, n<=64000.
"""
import sys
sys.dont_write_bytecode = True
import math
import numpy as np
import scipy
from scipy.fft import fft
from _common import BOUNDARY, emit_json, exact_inputs, odd_sigma, parser, require


def scaled_integer_float(value, n, rho, constant):
    # Conversion through a Decimal ratio avoids overflow of a(n) and cancellation
    # from separately rounded logarithms. This is an input overlap check, not the
    # FFT coefficient-extraction route itself.
    from decimal import Decimal, localcontext
    with localcontext() as ctx:
        ctx.prec = 60
        rho_d = Decimal(1) - (-Decimal(1)).exp()
        pi_d = Decimal("3.14159265358979323846264338327950288419716939937510582097494459")
        constant_d = pi_d*pi_d / (12 * (Decimal(1).exp() - 1))
        normalized = Decimal(value) * rho_d**n / Decimal(math.factorial(n))
        return float((normalized - constant_d) * Decimal(n)**Decimal(".75"))


def run(points=262144, kappa=40., modes=80, standalone=False):
    require(points in (262144, 524288), "points must be 262144 or 524288")
    require(kappa == 40. and modes == 80, "this bounded regression fixes kappa=40 and modes=80")
    rho, mu = 1 - math.exp(-1), math.e - 1
    constant = math.pi**2 / (12 * mu)
    z = np.exp(-kappa/points + 2j*np.pi*np.arange(points)/points)
    t = -np.log(-np.log(1-rho*z))
    inverse_t = 1/t
    minimum_real = float(np.min(inverse_t.real))
    require(minimum_real > 0, "eta mode expansion left the checked right half-plane")
    transformed = math.pi**2/(12*t) - math.log(2)/2 + t/24
    for m in range(1, modes+1):
        transformed -= (odd_sigma(m)/m) * np.exp(-2*math.pi**2*m/t)
    coeffs = fft(transformed - constant/(1-z)) / points
    max_imaginary = float(np.max(np.abs(coeffs[1:64001].imag)))
    require(max_imaginary < 1e-10, "FFT imaginary leakage regression")
    values, engine = exact_inputs(2000, standalone)
    rows, max_overlap = [], 0.
    for n in (100, 200, 400, 800, 1000, 2000, 4000, 8000, 16000, 32000, 64000):
        scaled = float((coeffs[n]*math.exp(kappa*n/points)).real * n**.75)
        h0, h1 = 0., 0.
        for m in range(1, 20):
            A = 2*math.pi**2*m/mu
            weight = (odd_sigma(m)/m) * math.exp(-A/2) * A**.25/math.sqrt(math.pi)
            phase = 2*math.sqrt(A*n)+math.pi/4
            D = ((4-8*mu**2)*A*A-9)/(48*math.sqrt(A))
            h0 -= weight*math.cos(phase)
            h1 -= weight*D*math.sin(phase)
        residual = (scaled-h0-h1/math.sqrt(n))*n
        require(math.isfinite(scaled) and abs(residual) < 1, f"FFT finite residual regression n={n}")
        row = {"n": n, "scaled_error": scaled, "H0": h0,
               "H0_H1": h0+h1/math.sqrt(n), "after_H1_times_n": residual}
        if n <= 2000:
            exact_scaled = scaled_integer_float(values[n], n, rho, constant)
            overlap = abs(scaled-exact_scaled)
            max_overlap = max(max_overlap, overlap)
            require(overlap < 1e-7, f"FFT versus exact-input overlap regression n={n}")
            row.update({"exact_input_scaled_error": exact_scaled, "absolute_overlap_error": overlap})
        rows.append(row)
    return {"schema_version": 1, "status": "PASS", "diagnostic": "fft_eta_extraction",
            "points": points, "kappa": kappa, "eta_modes": modes, "harmonic_modes": 19,
            "arithmetic": "IEEE 754 binary64; 60-digit Decimal for integer overlap only",
            "exact_input_engine": engine, "min_Re_inverse_t": minimum_real,
            "max_imaginary_coefficient": max_imaginary, "rows": rows,
            "checks": {"maximum_exact_overlap_error": max_overlap,
                       "exact_overlap_error_limit_exclusive": 1e-7,
                       "imaginary_leakage_limit_exclusive": 1e-10,
                       "absolute_after_H1_times_n_limit_exclusive": 1},
            "versions": {"numpy": np.__version__, "scipy": scipy.__version__}, "boundary": BOUNDARY,
            "fft_note": "Finite radius, grid aliasing, mode truncation and rounding errors are not enclosed. Point doubling is a diagnostic only."}


def main():
    p = parser(__doc__)
    p.add_argument("--points", type=int, default=262144)
    p.add_argument("--standalone", action="store_true")
    args = p.parse_args()
    emit_json(run(args.points, standalone=args.standalone), args.output)


if __name__ == "__main__":
    main()
