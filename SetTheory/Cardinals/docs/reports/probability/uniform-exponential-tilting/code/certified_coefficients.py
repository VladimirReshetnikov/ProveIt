#!/usr/bin/env python3
"""Certified sparse Fourier extraction of a Poisson-binomial probability.

Dependencies: Python >= 3.10 and python-flint >= 0.9.0.

The mathematical error bounds are those proved in the accompanying article.
Every transcendental operation and every quadrature operation uses Arb/Acb
ball arithmetic.  A returned interval includes analytic truncation errors as
well as arithmetic errors.  Input floats are deliberately rejected: use exact
integers, Fraction objects, decimal strings, or rational strings instead.

Public functions:
    certify_probability(probabilities, k, epsilon="1e-12", marginals=False)
    certify_coefficient(factors, k, epsilon="1e-12", marginals=False)

Each factor for the second function is a pair (a, b) representing a + b*z.
Nonnegative rational a and b are allowed, including deterministic factors.
The optional multiplicities argument repeats input groups without expanding
them.  Conditional marginals then refer to one representative copy per group.

JSON intervals have *exact* binary endpoints.  An endpoint with fields
``mantissa`` and ``exponent`` means int(mantissa) * 2**exponent.  The ``ball``
field is a readable Arb enclosure; exact endpoints are the authoritative
machine-readable certificate.  The string "-inf" is used for log(0).

The precision is increased until the ratio of the returned upper and lower
probability bounds is at most 1 + epsilon.  Thus any point in the returned
interval approximates the truth within relative error epsilon.  Conditional
marginal intervals, when requested, additionally have width <= epsilon.

The O(n log(1/epsilon)) arithmetic claim concerns extraction after a coarse
tilt.  This implementation uses separately counted bracket expansion and
bisection to find that tilt.  Working precision, input parsing, output size,
and transcendental-function bit costs are not hidden in that arithmetic claim.

Command line:
    python certified_coefficients.py --input example.json --output answer.json

The input JSON has ``probabilities`` (or ``factors``), ``k``, and optionally
``epsilon``, ``marginals``, ``multiplicities``, ``initial_precision``, and
``max_precision``.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from typing import Any, Iterable, Sequence

from flint import acb, arb, ctx, fmpq


class CertificationError(RuntimeError):
    """The requested certificate was not obtained within the resource limit."""


class _NeedMorePrecision(Exception):
    pass


def _fraction(value: Any, name: str = "input") -> Fraction:
    if isinstance(value, bool):
        return Fraction(int(value))
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, fmpq):
        return Fraction(str(value))
    if isinstance(value, str):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"{name} is not a finite rational number") from exc
    raise TypeError(
        f"{name} must be an exact integer, Fraction, or rational/decimal string; "
        "binary floating-point inputs are not accepted"
    )


def _arbq(value: Fraction) -> arb:
    return arb(fmpq(value.numerator, value.denominator))


def _multiplicities(values: Iterable[int] | None, size: int) -> list[int]:
    result = [1] * size if values is None else list(values)
    if len(result) != size:
        raise ValueError("multiplicities must have the same length as the input groups")
    if any(not isinstance(value, int) or isinstance(value, bool) or value < 1 for value in result):
        raise ValueError("each multiplicity must be a positive integer")
    return result


def _le_exact(left: arb, right: arb) -> bool:
    """Compare exact finite dyadics without expanding their binary exponents.

    Converting an endpoint such as 2**(-10**12) to fmpq would allocate an
    enormous denominator.  Native Arb ordering compares the compact exact
    mantissa/exponent representations directly.
    """
    if not (left.is_exact() and right.is_exact()
            and left.is_finite() and right.is_finite()):
        raise AssertionError("exact finite endpoints required")
    return left <= right


def _upper_at_most_fraction(value: arb, limit: Fraction) -> bool:
    """Conservatively compare a ball upper bound to an exact rational limit.

    The comparison stays in compact ball arithmetic.  Rounding the limit
    down can cause a harmless extra precision attempt, never a false
    certificate.
    """
    if not value.is_finite():
        return False
    return _le_exact(value.upper(), _arbq(limit).lower())


def _ceil_upper(value: arb) -> int:
    if not value.is_finite():
        raise _NeedMorePrecision
    return int(value.upper().ceil().fmpz())


def _endpoint(value: arb) -> dict[str, Any]:
    mantissa, exponent = value.man_exp()
    return {"mantissa": str(mantissa), "exponent": int(exponent)}


def _interval(lower: arb, upper: arb) -> dict[str, Any]:
    if not (lower.is_finite() and upper.is_finite()):
        raise _NeedMorePrecision
    lower, upper = lower.lower(), upper.upper()
    if not _le_exact(lower, upper):
        raise AssertionError("reversed certificate endpoints")
    enclosure = lower.union(upper)
    return {
        "lower": _endpoint(lower),
        "upper": _endpoint(upper),
        "ball": enclosure.str(25),
    }


def _ball_interval(value: arb) -> dict[str, Any]:
    return _interval(value.lower(), value.upper())


def _zero_interval() -> dict[str, Any]:
    return _interval(arb(0), arb(0))


def _one_interval() -> dict[str, Any]:
    return _interval(arb(1), arb(1))


def interval_to_arb(interval: dict[str, Any]) -> arb:
    """Read the exact dyadic certificate into an Arb enclosure.

    Construct this at sufficient working precision if tightness is important.
    This helper always returns an enclosure, even at lower precision.
    """
    lo, hi = interval["lower"], interval["upper"]
    if lo == "-inf" and hi == "-inf":
        return arb.neg_inf()
    lower = arb((int(lo["mantissa"]), int(lo["exponent"])))
    upper = arb((int(hi["mantissa"]), int(hi["exponent"])))
    return lower.union(upper)


def _tilted_values(
    probabilities: Sequence[Fraction], multiplicities: Sequence[int],
    theta: Fraction, target: int
) -> tuple[list[arb], list[arb], arb, arb, arb]:
    """Return q, 1-q, mean, variance, and log(P(exp(theta))/exp(k theta)).

    The sign-dependent formula avoids unnecessarily large exponentials and
    computes both q and 1-q directly, without subtracting a rounded value near
    one.  All expressions refer to the exact rational theta supplied here.
    """
    theta_ball = _arbq(theta)
    positive = theta >= 0
    exp_small = (-theta_ball if positive else theta_ball).exp()
    q_values, complements = [], []
    mean, variance, log_sum = arb(0), arb(0), arb(0)
    for probability, multiplicity in zip(probabilities, multiplicities):
        p = _arbq(probability)
        complement = _arbq(1 - probability)
        if positive:
            denominator = p + complement * exp_small
            q = p / denominator
            q_complement = complement * exp_small / denominator
        else:
            denominator = complement + p * exp_small
            q = p * exp_small / denominator
            q_complement = complement / denominator
        q_values.append(q)
        complements.append(q_complement)
        mean += multiplicity * q
        variance += multiplicity * q * q_complement
        log_sum += multiplicity * denominator.log()
    multiplier = sum(multiplicities) - target if positive else -target
    log_normalizer = log_sum + multiplier * theta_ball
    return q_values, complements, mean, variance, log_normalizer


def _mean_position(mean: arb, target: int) -> int:
    """0 means the mean match is certified; +/-1 gives a bracket direction."""
    difference = mean - target
    if _le_exact(difference.abs_upper(), arb((1, -2))):
        return 0
    if difference.upper() < 0:
        return -1
    if difference.lower() > 0:
        return 1
    raise _NeedMorePrecision


def _find_tilt(
    probabilities: Sequence[Fraction], multiplicities: Sequence[int],
    target: int, max_steps: int = 4096
) -> tuple[Fraction, tuple[list[arb], list[arb], arb, arb, arb], int]:
    evaluations = 0

    def evaluate(theta: Fraction):
        nonlocal evaluations
        evaluations += 1
        if evaluations > max_steps:
            raise CertificationError("coarse-tilt iteration limit exceeded")
        values = _tilted_values(probabilities, multiplicities, theta, target)
        return values, _mean_position(values[2], target)

    theta = Fraction(0)
    values, position = evaluate(theta)
    if position == 0:
        return theta, values, evaluations
    direction = -position
    previous = theta
    distance = 1
    while True:
        theta = Fraction(direction * distance)
        values, new_position = evaluate(theta)
        if new_position == 0:
            return theta, values, evaluations
        if new_position != position:
            lower, upper = sorted((previous, theta))
            break
        previous = theta
        distance *= 2
    while True:
        theta = (lower + upper) / 2
        values, position = evaluate(theta)
        if position == 0:
            return theta, values, evaluations
        if position < 0:
            lower = theta
        else:
            upper = theta


def _grid(
    n: int, variance: arb, epsilon: Fraction
) -> tuple[arb, arb, arb, int, int, bool, arb, arb]:
    variance_low = variance.lower()
    if variance_low < 0:
        variance_low = arb(0)
    variance_high = variance.upper()
    if not _le_exact((variance_high - variance_low).upper(), arb((1, -3))):
        raise _NeedMorePrecision

    # L itself is an exact dyadic upper bound, so there is no uncertain
    # branch test or ceil applied to an interval straddling a threshold.
    ell = (_arbq(Fraction(1000) / epsilon).log()).upper()
    m = min(n + 1, _ceil_upper(2 * (variance_high * ell).sqrt() + 2 * ell))
    if _le_exact(variance_high, (2 * ell).lower()):
        j = m // 2
    else:
        if not variance_low > ell:
            raise _NeedMorePrecision
        j = min(m // 2, _ceil_upper(m * (ell / (8 * variance_low)).sqrt()))
    complete = j == m // 2
    if complete:
        fourier_error = arb(0)
    else:
        if j <= 0 or variance_low <= 0:
            raise AssertionError("invalid sparse Fourier cutoff")
        exponent = -8 * variance_low * j * j / (m * m)
        fourier_error = (m * exponent.exp() / (8 * variance_low * j)).upper()
    if m == n + 1:
        alias_error = arb(0)
    else:
        alias_error = (8 / ((variance_low + 1).sqrt() * ell.expm1())).upper()
    return ell, variance_low, variance_high, m, j, complete, fourier_error, alias_error


def _quadrature(
    q_values: Sequence[arb], complements: Sequence[arb],
    multiplicities: Sequence[int], target: int,
    m: int, j: int, marginals: bool,
) -> tuple[arb, list[arb] | None, int]:
    # j=0 is exact for the mass.  The joint numerator at j=0 is q_i.
    total = arb(1)
    numerators = [q for q in q_values] if marginals else None
    n = len(q_values)
    for frequency in range(1, j + 1):
        z = acb(fmpq(2 * frequency, m)).exp_pi_i()
        phase = acb(fmpq(-2 * frequency * target, m)).exp_pi_i()
        weight = 1 if (m % 2 == 0 and frequency == m // 2) else 2
        single_factors = [a + q * z for a, q in zip(complements, q_values)]
        factors = [factor ** multiplicity for factor, multiplicity in zip(single_factors, multiplicities)]
        if marginals:
            prefix = [acb(1)]
            for factor in factors:
                prefix.append(prefix[-1] * factor)
            product = prefix[-1]
            suffix = acb(1)
            assert numerators is not None
            for index in range(n - 1, -1, -1):
                removed_factor = single_factors[index] ** (multiplicities[index] - 1)
                joint = phase * z * q_values[index] * removed_factor * prefix[index] * suffix
                numerators[index] += weight * joint.real
                suffix *= factors[index]
        else:
            product = acb(1)
            for factor in factors:
                product *= factor
        total += weight * (phase * product).real
    total /= m
    if numerators is not None:
        numerators = [value / m for value in numerators]
    return total, numerators, j + 1


def _clip_probability_bounds(lower: arb, upper: arb) -> tuple[arb, arb]:
    lower, upper = lower.lower(), upper.upper()
    if lower < 0:
        lower = arb(0)
    if upper > 1:
        upper = arb(1)
    if not _le_exact(lower, upper):
        raise AssertionError("empty probability certificate")
    return lower, upper


def _log_width_is_small(logarithm: arb, epsilon: Fraction) -> tuple[bool, arb]:
    width = (logarithm.upper() - logarithm.lower()).expm1()
    return _upper_at_most_fraction(width, epsilon), width


def _negative_infinity() -> dict[str, Any]:
    return {"lower": "-inf", "upper": "-inf", "ball": "-inf"}


def _zero_result(n: int, k: int, epsilon: Fraction, coefficient: bool) -> dict[str, Any]:
    result = {
        "status": "zero_probability", "k": k, "n": n,
        "epsilon": str(epsilon), "probability": _zero_interval(),
        "log_probability": _negative_infinity(),
        "normalized_mass": _zero_interval(), "conditional_marginals": None,
        "stats": {"grid_size": 0, "retained_radius": 0, "node_count": 0,
                  "complex_evaluations": 0, "tilt_evaluations": 0},
        "certificate": {"exact_zero": True},
    }
    if coefficient:
        result["coefficient"] = _zero_interval()
        result["log_coefficient"] = _negative_infinity()
    return result


def _certify(
    probabilities: Sequence[Fraction], multiplicities: Sequence[int],
    k: int, epsilon: Fraction, *,
    marginals: bool, initial_precision: int, max_precision: int,
    scale_factors: Sequence[Fraction] | None = None,
) -> dict[str, Any]:
    if not isinstance(k, int) or isinstance(k, bool):
        raise TypeError("k must be an integer")
    if not 0 < epsilon < 1:
        raise ValueError("epsilon must lie strictly between zero and one")
    if initial_precision < 32 or max_precision < initial_precision:
        raise ValueError("require 32 <= initial_precision <= max_precision")
    n_original = sum(multiplicities)
    deterministic_ones = sum(m for probability, m in zip(probabilities, multiplicities) if probability == 1)
    active_indices = [i for i, probability in enumerate(probabilities) if 0 < probability < 1]
    active = [probabilities[i] for i in active_indices]
    active_multiplicities = [multiplicities[i] for i in active_indices]
    n = sum(active_multiplicities)
    target = k - deterministic_ones
    if target < 0 or target > n:
        return _zero_result(n_original, k, epsilon, scale_factors is not None)
    boundary = target == 0 or target == n
    theta: Fraction | None = None
    tilt_evaluations = 0
    precision = initial_precision
    attempts = 0
    while precision <= max_precision:
        attempts += 1
        try:
            with ctx.workprec(precision):
                log_scale = arb(0)
                if scale_factors is not None:
                    for scale, multiplicity in zip(scale_factors, multiplicities):
                        log_scale += multiplicity * _arbq(scale).log()
                if boundary:
                    log_probability = arb(0)
                    for probability, multiplicity in zip(active, active_multiplicities):
                        term = probability if target == n else 1 - probability
                        log_probability += multiplicity * _arbq(term).log()
                    mass_low, mass_high = arb(1), arb(1)
                    quadrature, fourier_error, alias_error = arb(1), arb(0), arb(0)
                    mean, variance = arb(target), arb(0)
                    variance_low, variance_high = arb(0), arb(0)
                    ell, m, j, complete, evaluations = arb(0), 0, 0, True, 0
                    conditional = None
                    if marginals:
                        conditional = []
                        for probability in probabilities:
                            outcome = int(probability == 1) if probability in (0, 1) else int(target == n)
                            conditional.append(_one_interval() if outcome else _zero_interval())
                else:
                    if theta is None:
                        theta, values, count = _find_tilt(active, active_multiplicities, target)
                        tilt_evaluations += count
                    else:
                        values = _tilted_values(active, active_multiplicities, theta, target)
                        tilt_evaluations += 1
                    q_values, complements, mean, variance, log_normalizer = values
                    if _mean_position(mean, target) != 0:
                        raise _NeedMorePrecision
                    ell, variance_low, variance_high, m, j, complete, fourier_error, alias_error = _grid(
                        n, variance, epsilon
                    )
                    quadrature, joint_values, evaluations = _quadrature(
                        q_values, complements, active_multiplicities, target, m, j, marginals
                    )
                    mass_low = (quadrature.lower() - fourier_error - alias_error).lower()
                    mass_high = (quadrature.upper() + fourier_error).upper()
                    proved_lower = (1 / (6 * (variance_high + 1).sqrt())).lower()
                    if mass_low < proved_lower:
                        mass_low = proved_lower
                    mass_low, mass_high = _clip_probability_bounds(mass_low, mass_high)
                    if mass_low <= 0:
                        raise _NeedMorePrecision
                    mass_ball = mass_low.union(mass_high)
                    log_probability = log_normalizer + mass_ball.log()
                    conditional = None
                    if marginals:
                        assert joint_values is not None
                        active_marginals = []
                        for joint in joint_values:
                            # Removing one Bernoulli reduces variance by <=1/4,
                            # so e^(1/2)<2 multiplies the Fourier envelope.
                            joint_low = (joint.lower() - 2 * fourier_error - alias_error).lower()
                            joint_high = (joint.upper() + 2 * fourier_error).upper()
                            joint_low, joint_high = _clip_probability_bounds(joint_low, joint_high)
                            lower = (joint_low / mass_high).lower()
                            upper = (joint_high / mass_low).upper()
                            lower, upper = _clip_probability_bounds(lower, upper)
                            if not _upper_at_most_fraction(upper - lower, epsilon):
                                raise _NeedMorePrecision
                            active_marginals.append(_interval(lower, upper))
                        conditional = []
                        active_position = 0
                        for probability in probabilities:
                            if probability == 0:
                                conditional.append(_zero_interval())
                            elif probability == 1:
                                conditional.append(_one_interval())
                            else:
                                conditional.append(active_marginals[active_position])
                                active_position += 1
                log_coefficient = log_probability + log_scale
                success, relative_width = _log_width_is_small(log_coefficient, epsilon)
                probability_success, probability_width = _log_width_is_small(log_probability, epsilon)
                if not success or not probability_success:
                    raise _NeedMorePrecision
                probability_ball = log_probability.exp()
                # The returned probability endpoints, including exp rounding,
                # must meet the requested ratio criterion too.
                probability_ratio = probability_ball.upper() / probability_ball.lower() - 1
                if not _upper_at_most_fraction(probability_ratio, epsilon):
                    raise _NeedMorePrecision
                node_count = m if complete else 2 * j + 1
                result = {
                    "status": "certified", "n": n_original, "k": k,
                    "epsilon": str(epsilon),
                    "probability": _ball_interval(probability_ball),
                    "log_probability": _ball_interval(log_probability),
                    "normalized_mass": _interval(mass_low, mass_high),
                    "conditional_marginals": conditional,
                    "stats": {
                        "active_n": n, "active_k": target,
                        "input_groups": len(probabilities), "active_groups": len(active),
                        "multiplicities": list(multiplicities),
                        "group_power_work_bound": sum(multiplicity.bit_length() for multiplicity in active_multiplicities),
                        "deterministic_ones": deterministic_ones,
                        "precision_bits": precision, "precision_attempts": attempts,
                        "theta": str(theta) if theta is not None else None,
                        "mean": _ball_interval(mean), "variance": _ball_interval(variance),
                        "variance_lower": _endpoint(variance_low),
                        "variance_upper": _endpoint(variance_high),
                        "L": _ball_interval(ell), "grid_size": m,
                        "retained_radius": j, "node_count": node_count,
                        "complex_evaluations": evaluations,
                        "tilt_evaluations": tilt_evaluations,
                        "complete_grid": complete, "boundary_case": boundary,
                    },
                    "certificate": {
                        "mean_error_at_most": "1/4" if not boundary else "0",
                        "quadrature": _ball_interval(quadrature),
                        "alias_absolute_bound": _ball_interval(alias_error),
                        "fourier_absolute_bound": _ball_interval(fourier_error),
                        "relative_width_bound": _ball_interval(probability_ratio),
                        "log_relative_width_bound": _ball_interval(probability_width),
                        "marginal_absolute_width_at_most": str(epsilon) if marginals else None,
                        "endpoint_format": "exact mantissa * 2^exponent",
                        "arithmetic": "Arb/Acb ball arithmetic; exact rational input and tilt",
                    },
                }
                if scale_factors is not None:
                    coefficient_ball = log_coefficient.exp()
                    coefficient_ratio = coefficient_ball.upper() / coefficient_ball.lower() - 1
                    if not _upper_at_most_fraction(coefficient_ratio, epsilon):
                        raise _NeedMorePrecision
                    result["coefficient"] = _ball_interval(coefficient_ball)
                    result["log_coefficient"] = _ball_interval(log_coefficient)
                    result["certificate"]["coefficient_relative_width_bound"] = _ball_interval(coefficient_ratio)
                return result
        except _NeedMorePrecision:
            if precision == max_precision:
                break
            precision = min(2 * precision, max_precision)
    raise CertificationError(
        f"could not certify relative width <= {epsilon} within {max_precision} bits; "
        "no uncertified approximation has been returned"
    )


def certify_probability(
    probabilities: Iterable[Any], k: int, epsilon: Any = "1e-12", *,
    marginals: bool = False, multiplicities: Iterable[int] | None = None,
    initial_precision: int = 80,
    max_precision: int = 4096,
) -> dict[str, Any]:
    """Certify Pr(sum Bernoulli(p_i)=k), optionally all conditional marginals."""
    parsed = [_fraction(value, f"probability[{i}]") for i, value in enumerate(probabilities)]
    if any(value < 0 or value > 1 for value in parsed):
        raise ValueError("all probabilities must belong to [0,1]")
    counts = _multiplicities(multiplicities, len(parsed))
    return _certify(
        parsed, counts, k, _fraction(epsilon, "epsilon"), marginals=marginals,
        initial_precision=initial_precision, max_precision=max_precision,
    )


def certify_coefficient(
    factors: Iterable[Sequence[Any]], k: int, epsilon: Any = "1e-12", *,
    marginals: bool = False, multiplicities: Iterable[int] | None = None,
    initial_precision: int = 80,
    max_precision: int = 4096,
) -> dict[str, Any]:
    """Certify [z^k] product(a_i+b_i*z), for nonnegative rational factors.

    The accompanying probability is for p_i=b_i/(a_i+b_i).  Conditional
    marginals refer to the weighted k-subset law associated with the product.
    """
    probabilities, scales = [], []
    for index, factor in enumerate(factors):
        if len(factor) != 2:
            raise ValueError(f"factor[{index}] must have exactly two entries")
        a, b = (_fraction(value, f"factor[{index}]") for value in factor)
        if a < 0 or b < 0:
            raise ValueError("factor coefficients must be nonnegative")
        scale = a + b
        scales.append(scale)
        probabilities.append(b / scale if scale else Fraction(0))
    epsilon_fraction = _fraction(epsilon, "epsilon")
    counts = _multiplicities(multiplicities, len(probabilities))
    if any(scale == 0 for scale in scales):
        if not isinstance(k, int) or isinstance(k, bool):
            raise TypeError("k must be an integer")
        if not 0 < epsilon_fraction < 1:
            raise ValueError("epsilon must lie strictly between zero and one")
        result = _zero_result(sum(counts), k, epsilon_fraction, True)
        result["status"] = "zero_polynomial"
        result["probability"] = None
        result["log_probability"] = None
        return result
    return _certify(
        probabilities, counts, k, epsilon_fraction, marginals=marginals,
        initial_precision=initial_precision, max_precision=max_precision,
        scale_factors=scales,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", required=True, help="JSON input path")
    parser.add_argument("--output", help="JSON output path (default: standard output)")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as source:
        payload = json.load(source)
    options = {key: payload[key] for key in (
        "epsilon", "marginals", "multiplicities", "initial_precision", "max_precision"
    ) if key in payload}
    if "probabilities" in payload and "factors" in payload:
        parser.error("provide either probabilities or factors, not both")
    if "factors" in payload:
        result = certify_coefficient(payload["factors"], payload["k"], **options)
    else:
        result = certify_probability(payload["probabilities"], payload["k"], **options)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as destination:
            destination.write(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
