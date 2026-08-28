#!/usr/bin/env python3
"""Numerical and exact experiments for the Fabius/Rvachev integral report.

The script deliberately avoids sampling the Fabius distribution.  Instead it uses
identities proved in the report:

  * the positive-moment recurrence for Y = sum 2^{-k} U_k;
  * Newton series for the entire Mellin function M(s) = E[Y**s];
  * the centered-moment formula for B(s) = E[(1+Y)**(-s)];
  * the stable recurrence for negative moments;
  * the infinite sinc product for the characteristic function of Rvachev's up law.

The long floating-point recurrence below is positive and cancellation-free.  It
constructs a normalized Binomial(n, 1/2) probability vector around its mode, so
it does not overflow even for thousands of moments.  Exact rational moments are
computed separately for the small orders displayed in the paper.

Dependencies: Python >= 3.10, numpy, scipy, mpmath.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import mpmath as mp
import numpy as np
from scipy.integrate import quad


def exact_moments(max_n: int) -> list[Fraction]:
    """Return exact moments m_n = E[Y^n] through max_n.

    From Y = (U + Y')/2 with U uniform on [0,1],

        (2^n - 1) m_n = sum_{k=0}^{n-1} binom(n,k) m_k/(n-k+1).
    """
    moments = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        total = sum(
            Fraction(math.comb(n, k), n - k + 1) * moments[k]
            for k in range(n)
        )
        moments.append(total / (2**n - 1))
    return moments


def fast_moments(max_n: int) -> np.ndarray:
    """Compute many moments in extended precision without huge binomial integers.

    Writing J ~ Binomial(n,1/2), the recurrence is

        m_n = (1-2^{-n})^{-1} E[m_{n-J}/(J+1); J>=1].

    The binomial probability vector is generated relative to its modal entry and
    normalized in ``longdouble``.  All terms are nonnegative, so the computation
    is numerically well conditioned.
    """
    dtype = np.longdouble
    moments = np.zeros(max_n + 1, dtype=dtype)
    moments[0] = 1

    for n in range(1, max_n + 1):
        mode = n // 2
        probabilities = np.empty(n + 1, dtype=dtype)
        probabilities[mode] = 1

        if mode > 0:
            j = np.arange(mode, 0, -1, dtype=dtype)
            # p_{j-1}/p_j = j/(n-j+1)
            probabilities[mode - 1 :: -1] = np.cumprod(
                j / (dtype(n) - j + 1), dtype=dtype
            )

        if mode < n:
            j = np.arange(mode, n, dtype=dtype)
            # p_{j+1}/p_j = (n-j)/(j+1)
            probabilities[mode + 1 :] = np.cumprod(
                (dtype(n) - j) / (j + 1), dtype=dtype
            )

        probabilities /= np.sum(probabilities, dtype=dtype)
        weights = probabilities[1:] / np.arange(2, n + 2, dtype=dtype)
        moments[n] = np.dot(weights, moments[n - 1 :: -1])

        # Beyond this point 2^{-n} is far below the working precision.
        if n < 16384:
            moments[n] /= 1 - dtype(2) ** (-n)

    return moments


def newton_mellin(s: mp.mpf | mp.mpc, moments: np.ndarray) -> mp.mpf | mp.mpc:
    """Evaluate M(s)=E[Y^s] by its locally uniformly convergent Newton series."""
    s = mp.mpc(s) if isinstance(s, complex) else mp.mpf(s)
    coefficient = mp.mpf(1)  # (-1)^k binom(s,k), initially k=0
    total = mp.mpf(str(moments[0]))
    for k in range(1, len(moments)):
        coefficient *= (k - 1 - s) / k
        term = coefficient * mp.mpf(str(moments[k]))
        total += term
    return total


def negative_initial(theta: mp.mpf, moments: np.ndarray) -> mp.mpf:
    """Compute A(theta)=M(-theta) for theta>0 via a positive Newton series."""
    theta = mp.mpf(theta)
    coefficient = mp.mpf(1)  # (theta)_k/k!
    total = mp.mpf(str(moments[0]))
    for k in range(1, len(moments)):
        coefficient *= (theta + k - 1) / k
        total += coefficient * mp.mpf(str(moments[k]))
    return total


def centered_even_moment(j: int, moments: np.ndarray) -> mp.mpf:
    """Return mu_{2j}=E[(2Y-1)^(2j)] using mu_{2j}=2m_{2j+1}/(2j+1)."""
    if j == 0:
        return mp.mpf(1)
    return 2 * mp.mpf(str(moments[2 * j + 1])) / (2 * j + 1)


def shifted_negative_moment(s: mp.mpf, moments: np.ndarray) -> mp.mpf:
    r"""Compute B(s)=E[(1+Y)^(-s)] from the rapidly convergent centered series.

        B(s) = (2/3)^s sum_{j>=0} (s)_{2j} mu_{2j}/((2j)! 3^(2j)).
    """
    s = mp.mpf(s)
    coefficient = mp.mpf(1)
    total = mp.mpf(0)
    max_j = (len(moments) - 2) // 2

    for j in range(max_j + 1):
        if j:
            coefficient *= (
                (s + 2 * j - 2)
                * (s + 2 * j - 1)
                / ((2 * j - 1) * (2 * j) * 9)
            )
        term = coefficient * centered_even_moment(j, moments)
        total += term
        if j > 80 and abs(term) < mp.mpf("1e-55") * max(1, abs(total)):
            break

    return mp.power(mp.mpf(2) / 3, s) * total


def negative_moment_table(
    max_r: int, moments: np.ndarray
) -> tuple[list[mp.mpf], list[mp.mpf]]:
    """Return A(r)=M(-r) and normalized C_r for r=1,...,max_r."""
    a_values: list[mp.mpf] = []
    c_values: list[mp.mpf] = []

    a = negative_initial(mp.mpf(1), moments)
    c = a / 2  # Gamma(1) A(1) / 2^{1(2)/2}

    for r in range(1, max_r + 1):
        a_values.append(a)
        c_values.append(c)
        if r < max_r:
            b = shifted_negative_moment(mp.mpf(r), moments)
            rho = b / a
            a = mp.power(2, r + 1) * (a - b) / r
            c *= 1 - rho

    return a_values, c_values


def phase_constant(theta: str, moments: np.ndarray, steps: int = 35) -> mp.mpf:
    """Approximate the 1-periodic limiting profile C(theta)."""
    th = mp.mpf(theta)
    a = negative_initial(th, moments)
    c = mp.gamma(th) * a / mp.power(2, th * (th + 1) / 2)

    for j in range(steps):
        s = th + j
        b = shifted_negative_moment(s, moments)
        rho = b / a
        c *= 1 - rho
        a = mp.power(2, s + 1) * (a - b) / s
    return c


def sinc_product(t: float, factors: int = 60) -> float:
    """Characteristic function phi(t)=prod sin(t/2^k)/(t/2^k)."""
    if t == 0:
        return 1.0
    k = np.arange(1, factors + 1, dtype=float)
    # numpy.sinc(x)=sin(pi*x)/(pi*x)
    return float(np.prod(np.sinc(t / (math.pi * (2.0**k)))))


def integrate_with_zeros(function, cutoff: float) -> tuple[float, float]:
    """Integrate on [0,cutoff], supplying zeros 2*pi*n as break points."""
    zeros = [
        2 * math.pi * n
        for n in range(1, int(cutoff / (2 * math.pi)) + 1)
    ]
    return quad(
        function,
        0.0,
        cutoff,
        epsabs=2e-13,
        epsrel=2e-13,
        limit=3000,
        points=zeros,
    )


def correlation_constants(cutoff: float = 250.0) -> tuple[float, float]:
    """Compute the Gini integral and ||up||_2^2 from the sinc product.

    For the Gini integral we use the exact tail decomposition

        int_T^infty (1-phi(t)^2)/t^2 dt
        = 1/T - int_T^infty phi(t)^2/t^2 dt.

    The omitted correction is bounded using the first several sinc factors; with
    the default cutoff it is far below the displayed digits.
    """

    def gini_integrand(t: float) -> float:
        if abs(t) < 1e-7:
            return 1.0 / 9.0  # Var(Z)
        value = sinc_product(t)
        return (1.0 - value * value) / (t * t)

    def l2_integrand(t: float) -> float:
        value = sinc_product(t)
        return value * value

    gini_raw, _ = integrate_with_zeros(gini_integrand, cutoff)
    l2_raw, _ = integrate_with_zeros(l2_integrand, cutoff)

    gini = (gini_raw + 1.0 / cutoff) / (2.0 * math.pi)
    l2 = l2_raw / math.pi
    return gini, l2


def fraction_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def write_outputs(output_dir: Path, results: dict) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "numerical_results.json").write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    tex = r"""%% Generated by experiments.py; do not edit by hand.
\begin{tabular}{@{}ll@{}}
\toprule
Quantity & Numerical value \\
\midrule
$\mathfrak M(1/2)$ & \num{%(mhalf)s} \\
$\mathfrak M(-1/2)$ & \num{%(mneghalf)s} \\
$\mathfrak M(-1)$ & \num{%(mnegone)s} \\
$-\mathbb E\log Y$ & \num{%(logmoment)s} \\
$C_*$ & \num{%(cstar)s} \\
$\int_0^1F(1-F)$ & \num{%(gini)s} \\
$\int_{\mathbb R}\operatorname{up}(x)^2\,dx$ & \num{%(l2)s} \\
\bottomrule
\end{tabular}
""" % {
        "mhalf": results["mellin_values"]["0.5"],
        "mneghalf": results["mellin_values"]["-0.5"],
        "mnegone": results["mellin_values"]["-1"],
        "logmoment": results["minus_expected_log_y"],
        "cstar": results["negative_moment_constant"],
        "gini": results["gini_integral"],
        "l2": results["up_l2_squared"],
    }
    (output_dir / "numerical_results.tex").write_text(tex, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--moments",
        type=int,
        default=12000,
        help="number of floating moments (default: 12000)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for JSON/TeX output",
    )
    parser.add_argument(
        "--cutoff",
        type=float,
        default=500.0,
        help="Fourier integration cutoff (default: 500)",
    )
    args = parser.parse_args()

    if args.moments < 100:
        parser.error("--moments must be at least 100")

    mp.mp.dps = 60
    exact = exact_moments(12)
    moments = fast_moments(args.moments)

    mellin_points = ["-1", "-0.5", "0.5", "1.5", "2.5"]
    mellin = {
        point: mp.nstr(newton_mellin(mp.mpf(point), moments), 18)
        for point in mellin_points
    }

    a_values, c_values = negative_moment_table(20, moments)
    c_star = c_values[-1]
    phases = {
        theta: mp.nstr(phase_constant(theta, moments), 20)
        for theta in ["0.1", "0.25", "0.5", "0.75", "1.0"]
    }

    gini, l2 = correlation_constants(args.cutoff)
    log_moment = np.sum(
        moments[1:] / np.arange(1, len(moments), dtype=np.longdouble),
        dtype=np.longdouble,
    )

    results = {
        "floating_moments_used": args.moments,
        "exact_moments_m0_to_m12": [fraction_string(x) for x in exact],
        "mellin_values": mellin,
        "minus_expected_log_y": np.format_float_scientific(
            log_moment, precision=17, unique=False, trim="k"
        ),
        "negative_moments_m_minus_1_to_minus_6": [
            mp.nstr(a_values[r - 1], 18) for r in range(1, 7)
        ],
        "normalized_constants_C1_to_C12": [
            mp.nstr(c_values[r - 1], 18) for r in range(1, 13)
        ],
        "negative_moment_constant": mp.nstr(c_star, 18),
        "log_Cstar_over_sqrt_2pi": mp.nstr(
            mp.log(c_star / mp.sqrt(2 * mp.pi)), 18
        ),
        "phase_samples": phases,
        "gini_integral": f"{gini:.15g}",
        "integral_F_squared": f"{0.5 - gini:.15g}",
        "up_l2_squared": f"{l2:.15g}",
        "fourier_cutoff": args.cutoff,
    }

    write_outputs(args.output_dir, results)
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
