"""Tests of distinct mathematical representations and explicit bounds.

Run from the package root: python -m pytest -q
The main cross-check uses a finite positive Bessel sum with a one-sided
alternating tail, independently of the Mellin-residue expansion.
"""

import sys
from pathlib import Path

import pytest
from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
import bose_crossover as bose


@pytest.fixture(autouse=True)
def precision():
    with mp.workdps(65):
        yield


@pytest.mark.parametrize("u", ["0", ".1", "1", "4", "12"])
def test_bessel_representation_against_quadrature(u):
    u = mp.mpf(u)
    integral = 2 * mp.quad(lambda x: mp.exp(-x**4 - u * x**2), [0, 1, mp.inf])
    assert mp.almosteq(bose.psi(u), integral, rel_eps=mp.mpf("1e-58"))


def test_coefficients_and_exact_trivial_zeros():
    for k in range(1, 45):
        direct = ((-1)**k * mp.gamma(mp.mpf(1)/4 + mp.mpf(k)/2)
                  * mp.zeta(1 - mp.mpf(k)/2) / (2 * mp.factorial(k)))
        coefficient = bose.regular_coefficient(k)
        if k >= 6 and k % 4 == 2:
            assert coefficient == 0
        else:
            assert mp.almosteq(coefficient, direct, rel_eps=mp.mpf("1e-58"))
    assert bose.normalized_coefficient(2) == -mp.mpf(1) / 16


def test_scaled_hurwitz_term_retains_relative_precision():
    # Without precision guarding the tiny Hurwitz zeta, this term can
    # lose more than twenty digits when multiplied by the gamma factor.
    actual = bose._asymptotic_term(mp.mpf(1), 24, 401)
    with mp.workdps(150):
        expected = (mp.gamma(mp.mpf("48.5"))/mp.factorial(24)
                    * mp.zeta(mp.mpf("25.25"), 401))
    assert mp.almosteq(actual, expected, rel_eps=mp.mpf("1e-58"))


@pytest.mark.parametrize("s", ["1", "2", "3.9"])
def test_convergent_series_against_independent_bessel_sum(s):
    small = bose.evaluate(s, method="small", abs_tol=mp.mpf("1e-30"))
    other = bose.accelerated_positive_sum(s, abs_tol=mp.mpf("1e-45"))
    # The independently derived one-sided reference interval is much
    # narrower than the Mellin-series error allowance.
    assert small.lower <= other.lower <= other.upper <= small.upper
    assert not small.rounding_certified
    assert small.truncation_error_bound < mp.mpf("1e-30")


@pytest.mark.parametrize("terms", [1, 2, 3, 4, 7, 8])
def test_large_s_remainder_has_claimed_sign(terms):
    s = mp.mpf("3")
    reference = bose.evaluate(s, method="small", abs_tol=mp.mpf("1e-48"))
    asymptotic = bose.large_s_expansion(s, terms)
    assert asymptotic.lower <= reference.lower <= reference.upper <= asymptotic.upper
    if terms % 2:
        assert asymptotic.value == asymptotic.upper
    else:
        assert asymptotic.value == asymptotic.lower


def test_positive_sum_tail_bounds():
    s, n = mp.mpf("3"), 10
    reference = bose.evaluate(s, method="small", abs_tol=mp.mpf("1e-45"))
    finite = mp.fsum(bose.psi(s * mp.sqrt(k))/k for k in range(1, n + 1))
    lower = bose.direct_sum_tail_lower_bound(s, n)
    upper = bose.direct_sum_tail_upper_bound(s, n)
    assert lower <= reference.lower - finite <= reference.upper - finite <= upper
    # Even ten terms leave a very large tail; they cannot support a
    # high-accuracy numerical claim merely because terms are decreasing.
    assert lower > 1


def test_large_parameter_limit():
    s = mp.mpf("100")
    result = bose.evaluate(s, abs_tol=mp.mpf("1e-45"))
    leading = mp.sqrt(mp.pi / s) * mp.zeta(mp.mpf(5) / 4)
    assert result.upper < leading
    assert abs(result.midpoint / leading - 1) < mp.mpf("1e-4")


def test_temperature_inverse_and_residual():
    rho, delta = mp.mpf(".1"), mp.mpf(".01")
    solution = bose.critical_temperature(rho, delta, relative_tol=mp.mpf("1e-38"))
    check = bose.critical_density(solution, delta, abs_tol=mp.mpf("1e-42"))
    assert abs(check / rho - 1) < mp.mpf("1e-37")
    errors = [abs(bose.inverse_approximation(rho, delta, order=k) - solution)
              for k in (0, 1, 2)]
    assert errors[2] < errors[1] / 100 < errors[0]
    _, w, t0 = bose.inverse_parameters(rho, delta)
    A = bose.density_prefactor() * mp.gamma(mp.mpf(1)/4)
    assert mp.almosteq(t0 * mp.log(8 * mp.exp(mp.pi/2) * t0 / delta**2),
                       2 * rho / A, rel_eps=mp.mpf("1e-58"))
    assert w > 0


def test_global_density_and_stiffness_scaling_bounds():
    temperature, delta, factor = mp.mpf(".7"), mp.mpf(".9"), mp.mpf(3)
    base = bose.critical_density(temperature, delta, abs_tol=mp.mpf("1e-40"))
    raised = bose.critical_density(factor*temperature, delta, abs_tol=mp.mpf("1e-40"))
    assert factor*base < raised < factor**(mp.mpf(5)/4)*base
    stiffened = bose.critical_density(temperature, factor*delta,
                                      abs_tol=mp.mpf("1e-40"))
    assert base/mp.sqrt(factor) < stiffened < base


@pytest.mark.parametrize("trial_ratio", [".8", "1", "1.2"])
def test_density_interval_converts_to_temperature_bracket(trial_ratio):
    rho, delta = mp.mpf(".1"), mp.mpf(".01")
    actual = bose.critical_temperature(rho, delta, relative_tol=mp.mpf("1e-40"))
    trial = actual*mp.mpf(trial_ratio)
    density = bose.critical_density(trial, delta, abs_tol=mp.mpf("1e-43"))
    allowance = mp.mpf("1e-28")
    result = bose.temperature_bracket_from_density(
        trial, rho, density-allowance, density+allowance)
    assert result.lower < actual < result.upper
    assert not result.rounding_certified


def test_rejects_reversed_density_interval():
    with pytest.raises(ValueError):
        bose.temperature_bracket_from_density(1, 1, 2, 1)


@pytest.mark.parametrize("bad", [0, -1, mp.inf, mp.nan])
def test_rejects_nonpositive_or_nonfinite_parameter(bad):
    with pytest.raises(ValueError):
        bose.evaluate(bad)


def test_adaptive_series_does_not_cross_convergence_radius():
    with pytest.raises(ValueError):
        bose.evaluate(bose.convergence_radius(), method="small")
    # A fixed finite contour expansion remains a legitimate bounded
    # approximation at the positive endpoint, even though geometric
    # adaptive convergence there would be an unsuitable algorithm.
    result = bose.small_s_expansion(bose.convergence_radius(), 30)
    assert result.truncation_error_bound > 0

