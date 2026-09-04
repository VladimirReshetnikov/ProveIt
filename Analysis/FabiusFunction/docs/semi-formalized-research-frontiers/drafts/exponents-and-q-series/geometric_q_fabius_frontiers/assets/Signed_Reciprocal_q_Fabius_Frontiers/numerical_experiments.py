#!/usr/bin/env python3
"""Exact and high-precision experiments for the signed/reciprocal q-Fabius report.

This script is deliberately self-contained.  Its exact calculations use
``fractions.Fraction`` and integer arithmetic; floating-point arithmetic is
used only for independent numerical checks and figures.

The normalized geometric q-Fabius variable is

    Y_q = (1-q) * sum_{j>=0} q**j U_j,

with independent U_j ~ Uniform[0,1] when |q|<1.  For |q|>1 the same moment
recurrence defines a normalized meromorphic germ rather than a probability
law.  The script verifies:

* the moment recurrence and Bernoulli cumulants;
* sign conjugacy q -> -q;
* reciprocal convolution inversion q -> 1/q;
* scale decimation q -> q**m (especially m=2);
* Gaussian-binomial position layers, including negative q;
* the q-Prouhet moment-transfer identity;
* the inverse-geometric endpoint values for q=1/2 and q=1/4;
* the Fabius--Pochhammer moment-polynomial recurrence and the observed
  odd-q-integer divisor through degree 16;
* finite-field and unitary-subspace normalizations at q=±2, ±4;
* analytic product identities to high precision.

It also creates CSV tables and five standalone figures used in the report.
No random sampling is used: all plotted densities are obtained by Fourier
inversion of finite truncations of their exact characteristic products.
"""

from __future__ import annotations

import cmath
import csv
import itertools
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
ASSETS = ROOT / "assets"
DATA = ROOT / "data"
ASSETS.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)


# ---------------------------------------------------------------------------
# Exact rational algebra
# ---------------------------------------------------------------------------



# Polynomials are represented by low-to-high exact rational coefficient lists.
# These small helpers avoid a dependency on a computer-algebra package and make
# the moment-polynomial evidence independently reproducible.
Polynomial = list[Fraction]


def poly_trim(poly: Polynomial) -> Polynomial:
    """Remove trailing zero coefficients, retaining one coefficient for zero."""
    result = list(poly)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_add(left: Polynomial, right: Polynomial) -> Polynomial:
    """Add two exact rational polynomials."""
    size = max(len(left), len(right))
    result = [Fraction(0)] * size
    for i in range(size):
        if i < len(left):
            result[i] += left[i]
        if i < len(right):
            result[i] += right[i]
    return poly_trim(result)


def poly_mul(left: Polynomial, right: Polynomial) -> Polynomial:
    """Multiply two exact rational polynomials."""
    result = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return poly_trim(result)


def poly_scale(poly: Polynomial, scalar: Fraction) -> Polynomial:
    """Multiply a polynomial by an exact scalar."""
    return poly_trim([scalar * coefficient for coefficient in poly])


def poly_shift(poly: Polynomial, degree: int) -> Polynomial:
    """Multiply a polynomial by q**degree."""
    if poly == [Fraction(0)]:
        return list(poly)
    return [Fraction(0)] * degree + list(poly)


def one_minus_q_power(power: int) -> Polynomial:
    """Return the coefficient list of 1-q**power."""
    result = [Fraction(0)] * (power + 1)
    result[0] = 1
    result[power] = -1
    return result


def q_integer_polynomial(order: int) -> Polynomial:
    """Return [order]_q=1+q+...+q**(order-1)."""
    return [Fraction(1)] * order


def poly_divmod_exact(dividend: Polynomial, divisor: Polynomial) -> tuple[Polynomial, Polynomial]:
    """Exact polynomial long division over Q."""
    numerator = poly_trim(dividend)
    denominator = poly_trim(divisor)
    if denominator == [Fraction(0)]:
        raise ZeroDivisionError("polynomial division by zero")
    if len(numerator) < len(denominator):
        return [Fraction(0)], numerator
    quotient = [Fraction(0)] * (len(numerator) - len(denominator) + 1)
    remainder = list(numerator)
    while len(remainder) >= len(denominator) and remainder != [Fraction(0)]:
        shift = len(remainder) - len(denominator)
        coefficient = remainder[-1] / denominator[-1]
        quotient[shift] += coefficient
        subtraction = poly_shift(poly_scale(denominator, coefficient), shift)
        remainder = poly_add(remainder, poly_scale(subtraction, Fraction(-1)))
    return poly_trim(quotient), poly_trim(remainder)


def polynomial_to_string(poly: Polynomial, variable: str = "q") -> str:
    """Human-readable exact polynomial, descending by degree."""
    terms: list[str] = []
    for degree in range(len(poly) - 1, -1, -1):
        coefficient = poly[degree]
        if coefficient == 0:
            continue
        sign = "-" if coefficient < 0 else "+"
        magnitude = abs(coefficient)
        if degree == 0:
            body = str(magnitude)
        else:
            coefficient_text = "" if magnitude == 1 else f"{magnitude}*"
            power_text = variable if degree == 1 else f"{variable}^{degree}"
            body = coefficient_text + power_text
        if not terms:
            terms.append(("-" if sign == "-" else "") + body)
        else:
            terms.append(f" {sign} {body}")
    return "".join(terms) if terms else "0"


def fabius_pochhammer_moment_polynomials(n_max: int) -> list[Polynomial]:
    """Build P_n(q) from the proved pole-cleared moment recurrence.

    P_0=1 and

      P_n(q) = sum_{k<n} q^k/(n-k+1)! *
               ((q;q)_{n-1}/(q;q)_k) * P_k(q).
    """
    polynomials: list[Polynomial] = [[Fraction(1)]]
    for n in range(1, n_max + 1):
        total: Polynomial = [Fraction(0)]
        for k in range(n):
            pochhammer_ratio: Polynomial = [Fraction(1)]
            for j in range(k + 1, n):
                pochhammer_ratio = poly_mul(
                    pochhammer_ratio, one_minus_q_power(j)
                )
            term = poly_mul(pochhammer_ratio, polynomials[k])
            term = poly_shift(term, k)
            term = poly_scale(term, Fraction(1, math.factorial(n - k + 1)))
            total = poly_add(total, term)
        polynomials.append(poly_trim(total))
    return polynomials


def q_binomial(n: int, k: int, q: Fraction) -> Fraction:
    """Evaluate the Gaussian coefficient [n choose k]_q exactly.

    The requested q values are rational and are not nontrivial roots of unity,
    so the product formula has no vanishing denominator.
    """
    if k < 0 or k > n:
        return Fraction(0)
    k = min(k, n - k)
    value = Fraction(1)
    for i in range(1, k + 1):
        value *= (1 - q ** (n - k + i)) / (1 - q ** i)
    return value


def normalized_moments(q: Fraction, n_max: int) -> list[Fraction]:
    """Moments of the normalized q-Fabius germ through order ``n_max``.

    The functional equation

        M_q(t) = E((1-q)t) M_q(qt),  E(z)=(exp(z)-1)/z,

    gives

      (1-q^n)m_n = sum_{k<n} C(n,k) (1-q)^(n-k) q^k m_k/(n-k+1).
    """
    moments = [Fraction(1)]
    for n in range(1, n_max + 1):
        rhs = Fraction(0)
        for k in range(n):
            rhs += (
                Fraction(math.comb(n, k), n - k + 1)
                * (1 - q) ** (n - k)
                * q ** k
                * moments[k]
            )
        denominator = 1 - q ** n
        if denominator == 0:
            raise ZeroDivisionError(f"q={q} is singular at moment order n={n}")
        moments.append(rhs / denominator)
    return moments


def convolve_moment_sequences(
    left: Sequence[Fraction],
    right: Sequence[Fraction],
    a: Fraction = Fraction(1),
    b: Fraction = Fraction(1),
) -> list[Fraction]:
    """Moments of ``a*X+b*Y`` for independent X,Y with supplied moments."""
    n_max = min(len(left), len(right)) - 1
    result: list[Fraction] = []
    for n in range(n_max + 1):
        total = Fraction(0)
        for k in range(n + 1):
            total += (
                math.comb(n, k)
                * a ** k
                * b ** (n - k)
                * left[k]
                * right[n - k]
            )
        result.append(total)
    return result


def affine_moments(
    moments: Sequence[Fraction], scale: Fraction, shift: Fraction
) -> list[Fraction]:
    """Moments of ``scale*X+shift`` from moments of X."""
    result: list[Fraction] = []
    for n in range(len(moments)):
        total = Fraction(0)
        for k in range(n + 1):
            total += (
                math.comb(n, k)
                * scale ** k
                * shift ** (n - k)
                * moments[k]
            )
        result.append(total)
    return result




def hankel_determinant(moment_sequence: Sequence[Fraction], order: int) -> Fraction:
    """Exact determinant det(m_{i+j})_{0<=i,j<order}.

    Fraction-preserving Gaussian elimination is sufficient for the modest
    orders used in the reproducibility table.
    """
    matrix = [
        [moment_sequence[i + j] for j in range(order)]
        for i in range(order)
    ]
    determinant = Fraction(1)
    for col in range(order):
        pivot = next((row for row in range(col, order) if matrix[row][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
            determinant = -determinant
        pivot_value = matrix[col][col]
        determinant *= pivot_value
        for j in range(col, order):
            matrix[col][j] /= pivot_value
        for row in range(col + 1, order):
            factor = matrix[row][col]
            if factor:
                for j in range(col, order):
                    matrix[row][j] -= factor * matrix[col][j]
    return determinant

def finite_uniform_sum_moments(weights: Sequence[Fraction], n_max: int) -> list[Fraction]:
    """Exact moments of sum_j weights[j]*U_j, U_j iid Uniform[0,1]."""
    moments = [Fraction(1)] + [Fraction(0)] * n_max
    for weight in weights:
        updated = [Fraction(0)] * (n_max + 1)
        for n in range(n_max + 1):
            total = Fraction(0)
            for k in range(n + 1):
                # E[(weight*U)^(n-k)] = weight^(n-k)/(n-k+1)
                total += (
                    math.comb(n, k)
                    * moments[k]
                    * weight ** (n - k)
                    / (n - k + 1)
                )
            updated[n] = total
        moments = updated
    return moments


def position_energy_layer(n: int, k: int, q: Fraction) -> Fraction:
    """Sum q^(sum of selected zero-based positions) over k-subsets."""
    total = Fraction(0)
    for subset in itertools.combinations(range(n), k):
        total += q ** sum(subset)
    return total


def prouhet_sum(n: int, m: int, q: Fraction) -> Fraction:
    """S_{n,m}(q)=sum_e (-1)^|e| (sum_j e_j q^j)^m, j=0..n-1."""
    total = Fraction(0)
    for mask in range(1 << n):
        point = Fraction(0)
        parity = 0
        for j in range(n):
            if (mask >> j) & 1:
                point += q ** j
                parity ^= 1
        total += (-1 if parity else 1) * point ** m
    return total


def grassmann_count(q_field: int, n: int, k: int) -> int:
    """Number of k-subspaces of F_q^n for prime-power q."""
    value = q_binomial(n, k, Fraction(q_field))
    if value.denominator != 1:
        raise AssertionError("Gaussian coefficient at a prime power must be integral")
    return value.numerator


def unitary_nondegenerate_count(q_field: int, n: int, k: int) -> int:
    """Count implied by Fu--Reiner--Stanton--Thiem's negative-q formula.

    If d=k(n-k), their normalization is

        [n choose k]_{-Q} = (-Q)^(-d) U_Q(n,k),

    where U_Q(n,k) counts nondegenerate k-subspaces of a Hermitian space over
    F_{Q^2}.  Hence U_Q(n,k)=(-Q)^d [n choose k]_{-Q}.
    """
    d = k * (n - k)
    value = Fraction((-q_field) ** d) * q_binomial(n, k, Fraction(-q_field))
    if value.denominator != 1 or value < 0:
        raise AssertionError("unitary count must be a nonnegative integer")
    return value.numerator


# ---------------------------------------------------------------------------
# Exact identity verification and CSV output
# ---------------------------------------------------------------------------

def verify_exact_identities() -> None:
    requested = [
        Fraction(1, 2),
        Fraction(-1, 2),
        Fraction(2),
        Fraction(-2),
        Fraction(1, 4),
        Fraction(-1, 4),
        Fraction(4),
        Fraction(-4),
    ]
    n_max = 10
    moment_map = {q: normalized_moments(q, n_max) for q in requested}

    # q -> -q affine conjugacy.  In centered form the scale is
    # lambda=(1+q)/(1-q); in raw form the shift is (1-lambda)/2.
    for q in [Fraction(1, 2), Fraction(2), Fraction(1, 4), Fraction(4)]:
        lam = (1 + q) / (1 - q)
        shift = (1 - lam) / 2
        predicted = affine_moments(moment_map[q], lam, shift)
        assert predicted == moment_map[-q]

    # q -> 1/q: M_q(t) M_{1/q}(-t)=1.  Check every coefficient through n_max.
    for q in [Fraction(1, 2), Fraction(-1, 2), Fraction(1, 4), Fraction(-1, 4)]:
        reciprocal = 1 / q
        for n in range(1, n_max + 1):
            coefficient = sum(
                Fraction(math.comb(n, k))
                * moment_map[q][k]
                * (-1) ** (n - k)
                * moment_map[reciprocal][n - k]
                for k in range(n + 1)
            )
            assert coefficient == 0

    # q -> q^2 decimation:
    # Y_q = Y_{q^2}^{(0)}/(1+q) + q Y_{q^2}^{(1)}/(1+q).
    for q in [Fraction(1, 2), Fraction(-1, 2), Fraction(2), Fraction(-2)]:
        q2 = q * q
        m2 = normalized_moments(q2, n_max)
        a = 1 / (1 + q)
        b = q / (1 + q)
        predicted = convolve_moment_sequences(m2, m2, a, b)
        assert predicted == moment_map[q]

    # Position-energy layers equal q^{k choose 2}[n choose k]_q.
    for q in requested:
        for n in range(1, 9):
            for k in range(n + 1):
                direct = position_energy_layer(n, k, q)
                gaussian = q ** (k * (k - 1) // 2) * q_binomial(n, k, q)
                assert direct == gaussian

    # q-Prouhet moment transfer, checked for every requested q.
    verification_rows: list[dict[str, str | int]] = []
    for q in requested:
        for n in range(1, 8):
            finite_moments = finite_uniform_sum_moments(
                [q ** j for j in range(n)], 4
            )
            for m in range(n):
                assert prouhet_sum(n, m, q) == 0
            for ell in range(5):
                lhs = prouhet_sum(n, n + ell, q)
                rhs = (
                    (-1) ** n
                    * Fraction(math.factorial(n + ell), math.factorial(ell))
                    * q ** (n * (n - 1) // 2)
                    * finite_moments[ell]
                )
                assert lhs == rhs
                verification_rows.append(
                    {
                        "q": str(q),
                        "N": n,
                        "ell": ell,
                        "S_N_N_plus_ell": str(lhs),
                        "predicted": str(rhs),
                        "residual": "0",
                    }
                )

    with (DATA / "q_prouhet_verification.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(verification_rows[0]))
        writer.writeheader()
        writer.writerows(verification_rows)

    # Moment table for the two Klein-four orbits requested by the prompt.
    with (DATA / "q_orbit_moments.csv").open("w", newline="") as f:
        fieldnames = ["q", "mean", "variance"] + [f"m_{n}" for n in range(7)]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for q in requested:
            m = moment_map[q]
            row: dict[str, str] = {
                "q": str(q),
                "mean": str(m[1]),
                "variance": str(m[2] - m[1] ** 2),
            }
            row.update({f"m_{n}": str(m[n]) for n in range(7)})
            writer.writerow(row)

    # Reciprocal germs have the exact Hankel signature
    # sign det(m_{i+j}) = (-1)^(order choose 2).  The report proves this by
    # representing the centered germ as the characteristic function of an
    # explicit infinite convolution of Laplace laws.
    hankel_rows: list[dict[str, str | int]] = []
    for q in [Fraction(2), Fraction(-2), Fraction(4), Fraction(-4)]:
        moments = normalized_moments(q, 18)
        for order in range(1, 10):
            determinant = hankel_determinant(moments, order)
            expected_sign = -1 if (order * (order - 1) // 2) % 2 else 1
            actual_sign = 1 if determinant > 0 else -1 if determinant < 0 else 0
            assert actual_sign == expected_sign
            hankel_rows.append(
                {
                    "q": str(q),
                    "order": order,
                    "determinant": str(determinant),
                    "actual_sign": actual_sign,
                    "expected_sign": expected_sign,
                }
            )
    with (DATA / "reciprocal_hankel_signatures.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(hankel_rows[0]))
        writer.writeheader()
        writer.writerows(hankel_rows)

    # Exact inverse-geometric endpoint values G_q(q^n), q=1/2 and q=1/4.
    endpoint_rows: list[dict[str, str | int]] = []
    for q in [Fraction(1, 2), Fraction(1, 4)]:
        m = normalized_moments(q, 14)
        for n in range(0, 13):
            value = (
                q ** (n * (n + 1) // 2)
                * m[n]
                / ((1 - q) ** n * math.factorial(n))
            )
            endpoint_rows.append(
                {
                    "q": str(q),
                    "n": n,
                    "argument_q^n": str(q ** n),
                    "moment_m_n": str(m[n]),
                    "G_q(q^n)": str(value),
                    "decimal": f"{float(value):.17e}",
                }
            )
    with (DATA / "inverse_geometric_endpoint_values.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(endpoint_rows[0]))
        writer.writeheader()
        writer.writerows(endpoint_rows)

    # Finite-field / unitary square.  These are exact integer checks.
    geometry_rows: list[dict[str, str | int]] = []
    for q_field in [2, 4]:
        for n in range(2, 8):
            for k in range(1, n):
                d = k * (n - k)
                gr = grassmann_count(q_field, n, k)
                unitary = unitary_nondegenerate_count(q_field, n, k)
                plus_recip = q_binomial(n, k, Fraction(1, q_field))
                minus_recip = q_binomial(n, k, Fraction(-1, q_field))
                assert plus_recip == Fraction(gr, q_field ** d)
                assert minus_recip == Fraction(unitary, q_field ** (2 * d))
                geometry_rows.append(
                    {
                        "Q": q_field,
                        "n": n,
                        "k": k,
                        "d=k(n-k)": d,
                        "Grassmann_count": gr,
                        "Unitary_nondegenerate_count": unitary,
                        "[n k]_(1/Q)": str(plus_recip),
                        "[n k]_(-1/Q)": str(minus_recip),
                    }
                )
    with (DATA / "grassmannian_unitary_square.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(geometry_rows[0]))
        writer.writeheader()
        writer.writerows(geometry_rows)




def verify_moment_polynomial_divisibility() -> None:
    """Verify the observed odd-q-integer divisor through degree 16.

    This is evidence for a conjecture, not a proof.  The recurrence itself is
    exact and proved in the report; the long division below certifies that the
    proposed divisor has zero remainder for every tested degree.
    """
    n_max = 16
    polynomials = fabius_pochhammer_moment_polynomials(n_max)
    rows: list[dict[str, str | int]] = []
    for n, polynomial in enumerate(polynomials):
        divisor: Polynomial = [Fraction(1)]
        for odd_order in range(3, n + 1, 2):
            divisor = poly_mul(divisor, q_integer_polynomial(odd_order))
        quotient, remainder = poly_divmod_exact(polynomial, divisor)
        divisible = remainder == [Fraction(0)]
        if n >= 3 and not divisible:
            raise AssertionError(f"odd-q-integer divisor failed at n={n}")
        rows.append(
            {
                "n": n,
                "P_n_degree": len(polynomial) - 1,
                "odd_q_integer_divisor_degree": len(divisor) - 1,
                "divisible": str(divisible),
                "quotient_degree": len(quotient) - 1,
                "P_n(q)": polynomial_to_string(polynomial),
                "quotient": polynomial_to_string(quotient),
            }
        )

    with (DATA / "moment_polynomial_divisibility.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


# ---------------------------------------------------------------------------
# High-precision analytic products
# ---------------------------------------------------------------------------

def E_mp(z: mp.mpc) -> mp.mpc:
    """Entire E(z)=(e^z-1)/z with stable removal at zero."""
    if abs(z) < mp.mpf("1e-40"):
        return mp.mpf(1)
    return mp.expm1(z) / z


def normalized_mgf_mp(q: mp.mpf, t: mp.mpc, terms: int = 300) -> mp.mpc:
    """High-precision normalized q-Fabius MGF/germ.

    * |q|<1: product from j=0 upward;
    * |q|>1: reciprocal product from j=1 upward.
    """
    if q == 0:
        return E_mp(t)
    if abs(q) < 1:
        product = mp.mpc(1)
        weight = 1 - q
        for j in range(terms):
            product *= E_mp(weight * (q ** j) * t)
        return product
    if abs(q) > 1:
        product = mp.mpc(1)
        weight = 1 - q
        for j in range(1, terms + 1):
            product *= E_mp(weight * (q ** (-j)) * t)
        return 1 / product
    raise ValueError("The unit circle is singular for this product representation")


def verify_numeric_products() -> None:
    mp.mp.dps = 90
    requested = [
        mp.mpf(1) / 2,
        -mp.mpf(1) / 2,
        mp.mpf(2),
        -mp.mpf(2),
        mp.mpf(1) / 4,
        -mp.mpf(1) / 4,
        mp.mpf(4),
        -mp.mpf(4),
    ]
    test_points = [mp.mpc("0.37", "0.21"), mp.mpc("-0.8", "0.13")]
    rows: list[dict[str, str]] = []

    for q in requested:
        for t in test_points:
            m = normalized_mgf_mp(q, t)
            functional = E_mp((1 - q) * t) * normalized_mgf_mp(q, q * t)
            functional_error = abs(m - functional)

            reciprocal = normalized_mgf_mp(1 / q, -t)
            inversion_error = abs(m * reciprocal - 1)

            q2 = q * q
            a = 1 / (1 + q)
            b = q / (1 + q)
            decimated = normalized_mgf_mp(q2, a * t) * normalized_mgf_mp(q2, b * t)
            decimation_error = abs(m - decimated)

            # Sign conjugacy uses lambda=(1+q)/(1-q).
            if q > 0:
                lam = (1 + q) / (1 - q)
                sign_predicted = mp.exp((1 - lam) * t / 2) * normalized_mgf_mp(q, lam * t)
                sign_error = abs(normalized_mgf_mp(-q, t) - sign_predicted)
            else:
                sign_error = mp.nan

            rows.append(
                {
                    "q": mp.nstr(q, 10),
                    "t": mp.nstr(t, 16),
                    "functional_error": mp.nstr(functional_error, 8),
                    "inversion_error": mp.nstr(inversion_error, 8),
                    "decimation_error": mp.nstr(decimation_error, 8),
                    "sign_error": mp.nstr(sign_error, 8),
                }
            )

    with (DATA / "analytic_product_errors.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    max_error = mp.mpf(0)
    for row in rows:
        for key in ["functional_error", "inversion_error", "decimation_error", "sign_error"]:
            if row[key] != "nan":
                max_error = max(max_error, mp.mpf(row[key]))
    # The products converge geometrically; 300 factors at 90 digits should be
    # vastly more than enough for the requested q values.
    if max_error > mp.mpf("1e-35"):
        raise AssertionError(f"unexpectedly large product residual: {max_error}")


# ---------------------------------------------------------------------------
# Deterministic Fourier inversion and figures
# ---------------------------------------------------------------------------

def centered_density_fft(q: float, grid_size: int = 2**16, period: float = 2.0):
    """Approximate the density of Y_q-1/2 for 0<q<1 by FFT inversion.

    The characteristic function in cycles-per-unit convention is

        product_j sinc((1-q) q^j f),

    where numpy.sinc(x)=sin(pi*x)/(pi*x).  The containing period is chosen
    larger than the compact support, suppressing periodic overlap.
    """
    dx = period / grid_size
    frequencies = np.fft.fftfreq(grid_size, d=dx)
    phi = np.ones(grid_size, dtype=np.float64)
    weight = 1.0 - q
    max_frequency = float(np.max(np.abs(frequencies)))
    j = 0
    while weight * max_frequency > 1e-11 and j < 80:
        phi *= np.sinc(weight * frequencies)
        weight *= q
        j += 1
    # Remaining factors differ from 1 by O((weight*f)^2), below the threshold.
    density = np.fft.ifft(phi).real / dx
    density = np.fft.fftshift(density)
    x = (np.arange(grid_size) - grid_size // 2) * dx
    density[np.abs(density) < 5e-11] = 0.0
    return x, density


def make_density_figures() -> None:
    positive_data = {}
    for q in [0.5, 0.25]:
        x_centered, density = centered_density_fft(q)
        positive_data[q] = (x_centered + 0.5, density)

    plt.figure(figsize=(8.4, 5.2))
    for q, (x, density) in positive_data.items():
        mask = (x >= -0.01) & (x <= 1.01)
        plt.plot(x[mask], density[mask], label=fr"$q={q:g}$")
    plt.xlabel(r"$x$")
    plt.ylabel(r"density $g_q(x)$")
    plt.title("Normalized positive q-Fabius densities")
    plt.legend()
    plt.tight_layout()
    plt.savefig(ASSETS / "positive_q_fabius_densities.png", dpi=220)
    plt.close()

    # Negative parameters are exact affine images of the positive laws.
    plt.figure(figsize=(8.4, 5.2))
    for a in [0.5, 0.25]:
        x_pos, d_pos = positive_data[a]
        lam = (1 + a) / (1 - a)
        beta = a / (1 - a)
        x_neg = lam * x_pos - beta
        d_neg = d_pos / lam
        plt.plot(x_neg, d_neg, label=fr"$q={-a:g}$")
    plt.xlabel(r"$x$")
    plt.ylabel(r"density $g_q(x)$")
    plt.title("Negative-q laws as affine images of positive-q laws")
    plt.legend()
    plt.tight_layout()
    plt.savefig(ASSETS / "negative_q_affine_densities.png", dpi=220)
    plt.close()


def comb_points(q: Fraction, n: int):
    points = []
    signs = []
    total_scale = sum((q ** j for j in range(n)), Fraction(0))
    for mask in range(1 << n):
        x = Fraction(0)
        parity = 0
        for j in range(n):
            if (mask >> j) & 1:
                x += q ** j
                parity ^= 1
        points.append(float(x / total_scale))
        signs.append(-1 if parity else 1)
    return np.asarray(points), np.asarray(signs)


def make_comb_figures() -> None:
    for q, name, title in [
        (Fraction(1, 2), "dyadic_thue_morse_comb.png", "Dyadic Thue--Morse derivative comb"),
        (Fraction(1, 4), "quartic_cantor_comb.png", "Quartic signed Cantor derivative comb"),
    ]:
        x, signs = comb_points(q, 9)
        plt.figure(figsize=(9.0, 3.4))
        plt.scatter(x, signs, s=8)
        plt.axhline(0, linewidth=0.8)
        plt.yticks([-1, 1], [r"$-1$", r"$+1$"])
        plt.xlabel("normalized knot position")
        plt.ylabel("Thue--Morse sign")
        plt.title(title + r" ($N=9$)")
        plt.tight_layout()
        plt.savefig(ASSETS / name, dpi=220)
        plt.close()


def make_endpoint_figure() -> None:
    q = Fraction(1, 4)
    moments = normalized_moments(q, 16)
    ns = np.arange(1, 16)
    values = []
    for n_value in ns:
        n = int(n_value)
        exact = (
            q ** (n * (n + 1) // 2)
            * moments[n]
            / ((1 - q) ** n * math.factorial(n))
        )
        values.append(-math.log10(float(exact)))
    plt.figure(figsize=(8.2, 5.0))
    plt.plot(ns, values, marker="o")
    plt.xlabel(r"$n$")
    plt.ylabel(r"$-\log_{10} G_{1/4}(4^{-n})$")
    plt.title("Superalgebraic decay on the inverse-quartic endpoint lattice")
    plt.tight_layout()
    plt.savefig(ASSETS / "quartic_endpoint_decay.png", dpi=220)
    plt.close()


def main() -> None:
    verify_exact_identities()
    verify_moment_polynomial_divisibility()
    verify_numeric_products()
    make_density_figures()
    make_comb_figures()
    make_endpoint_figure()
    print("All exact and high-precision checks passed.")
    print(f"Tables written to {DATA}")
    print(f"Figures written to {ASSETS}")


if __name__ == "__main__":
    main()
