#!/usr/bin/env python3
"""Exact finite-order coefficient checks for Report197 / OEIS A373271.

All arithmetic uses fractions.Fraction.  The calculations check algebraic
identities, Gaussian moments, and radial integrals after their stated analytic
reductions.  They do not certify analytic error bounds, asymptotic onset,
minor-arc localization, or any higher-order expansion.  No floating-point
comparison, numerical tolerance, or assert statement is used.

run() returns a deterministic, JSON-serializable object.  Executing this file
prints that object and returns a nonzero exit status if any identity fails.
"""

from fractions import Fraction as F
import json
import sys


class Poly:
    """Sparse Laurent polynomials over Q, with the relation u**4 = 6.

    A monomial is a sorted tuple of (symbol, integer exponent) pairs.  All
    symbols except u are algebraically independent.  Here u denotes 6**(1/4),
    r denotes sqrt(A), and sqrt_pi is an integral-normalization symbol.
    """

    def __init__(self, terms=None):
        self.terms = {}
        for monomial, coefficient in (terms or {}).items():
            coefficient = F(coefficient)
            powers = dict(monomial)
            if "u" in powers:
                quotient, remainder = divmod(powers["u"], 4)
                coefficient *= F(6) ** quotient
                powers["u"] = remainder
            key = tuple(sorted((name, power) for name, power in powers.items() if power))
            self.terms[key] = self.terms.get(key, F(0)) + coefficient
        self.terms = {key: coefficient for key, coefficient in self.terms.items() if coefficient}

    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly({(): F(value)})

    def __add__(self, other):
        terms = dict(self.terms)
        for key, value in Poly.lift(other).terms.items():
            terms[key] = terms.get(key, F(0)) + value
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly.lift(other))

    def __rsub__(self, other):
        return Poly.lift(other) - self

    def __mul__(self, other):
        result = {}
        for left, a in self.terms.items():
            for right, b in Poly.lift(other).terms.items():
                powers = dict(left)
                for name, power in right:
                    powers[name] = powers.get(name, 0) + power
                key = tuple(sorted(powers.items()))
                result[key] = result.get(key, F(0)) + a * b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError("Only integer powers are supported")
        if exponent < 0:
            if len(self.terms) != 1:
                raise ValueError("Negative powers require a nonzero monomial")
            (monomial, coefficient), = self.terms.items()
            return Poly({tuple((name, power * exponent) for name, power in monomial):
                         coefficient ** exponent})
        result = Poly.lift(1)
        factor = self
        while exponent:
            if exponent % 2:
                result = result * factor
            factor = factor * factor
            exponent //= 2
        return result

    def __truediv__(self, other):
        return self * (Poly.lift(other) ** -1)

    def __rtruediv__(self, other):
        return Poly.lift(other) / self

    def __eq__(self, other):
        return self.terms == Poly.lift(other).terms

    def coefficient(self, symbol, exponent):
        return Poly({tuple((name, power) for name, power in monomial if name != symbol): value
                     for monomial, value in self.terms.items()
                     if dict(monomial).get(symbol, 0) == exponent})

    def truncate(self, symbol, maximum):
        return Poly({monomial: value for monomial, value in self.terms.items()
                     if dict(monomial).get(symbol, 0) <= maximum})

    def substitute(self, symbol, replacement):
        result = Poly.lift(0)
        replacement = Poly.lift(replacement)
        for monomial, value in self.terms.items():
            powers = dict(monomial)
            exponent = powers.pop(symbol, 0)
            result += Poly({tuple(powers.items()): value}) * replacement ** exponent
        return result

    def text(self):
        if not self.terms:
            return "0"
        pieces = []
        for monomial, coefficient in sorted(self.terms.items()):
            factors = [str(coefficient)]
            factors += [name if power == 1 else name + "^" + str(power)
                        for name, power in monomial]
            pieces.append("*".join(factors))
        return " + ".join(pieces).replace(" + -", " - ")


def symbol(name):
    return Poly({((name, 1),): F(1)})


def geometric_inverse(z, order):
    """Finite Taylor polynomial of 1/(1+z); no remainder claim is made."""
    z = Poly.lift(z)
    return sum(((-z) ** j for j in range(order + 1)), Poly.lift(0))


def exponential(z, order):
    """Finite Taylor polynomial of exp(z)."""
    result = Poly.lift(1)
    term = Poly.lift(1)
    for j in range(1, order + 1):
        term = term * z / j
        result += term
    return result


def log_one_plus(z, order):
    return sum((F((-1) ** (j + 1), j) * z ** j for j in range(1, order + 1)),
               Poly.lift(0))


def binomial_one_plus(z, power, order):
    coefficient = F(1)
    result = Poly.lift(1)
    for j in range(1, order + 1):
        coefficient *= (F(power) - j + 1) / j
        result += coefficient * z ** j
    return result


def radial_integral(k):
    """Exact value of integral_0^infinity x^-k exp(-1/x^2) dx, k > 1.

    Uses I_2=sqrt(pi)/2, I_3=1/2 and I_(k+2)=(k-1) I_k/2,
    which follow from the gamma-integral substitution and integration by parts.
    """
    if not isinstance(k, int) or k < 2:
        raise ValueError("The integral requires an integer k >= 2")
    if k % 2 == 0:
        value = symbol("sqrt_pi") / 2
        first = 2
    else:
        value = Poly.lift(F(1, 2))
        first = 3
    for current in range(first, k, 2):
        value *= F(current - 1, 2)
    return value


def integrate_radial_profile(profile, coordinate):
    """Integrate a Laurent profile multiplied by exp(-1/coordinate**2)."""
    result = Poly.lift(0)
    for monomial, coefficient in profile.terms.items():
        powers = dict(monomial)
        exponent = powers.pop(coordinate, 0)
        result += Poly({tuple(powers.items()): coefficient}) * radial_integral(-exponent)
    return result


def gaussian_moment(degree):
    """Moment under exp(-v**2)/sqrt(pi), evaluated by exact recurrence."""
    if not isinstance(degree, int) or degree < 0:
        raise ValueError("The moment degree must be a nonnegative integer")
    if degree % 2:
        return F(0)
    result = F(1)
    for j in range(2, degree + 1, 2):
        result *= F(j - 1, 2)
    return result


def run():
    checks = []

    def check(name, obtained, expected, statement=None):
        obtained, expected = Poly.lift(obtained), Poly.lift(expected)
        residual = obtained - expected
        entry = {"name": name, "passed": residual == 0,
                 "obtained": obtained.text(), "expected": expected.text(),
                 "residual": residual.text()}
        if statement is not None:
            entry["statement"] = statement
        checks.append(entry)

    h, x, y = symbol("h"), symbol("x"), symbol("y")
    sp = symbol("sqrt_pi")
    d = F(12365, 82944)

    check("radial_I3", radial_integral(3), F(1, 2))
    check("radial_I4", radial_integral(4), sp / 4)
    check("radial_I6", radial_integral(6), 3 * sp / 8)
    f0_integral = 2 * radial_integral(2)
    check("radial_f0_by_integration_by_parts", f0_integral, sp)

    # x=h*m and y=h*(m+1/2) are independent coordinate calculations.
    a_nc = (x ** -2 * geometric_inverse(h / x, 2)).truncate("h", 2)
    a_c = (y ** -2 * geometric_inverse(-h ** 2 / (4 * y ** 2), 2)).truncate("h", 2)
    check("A_noncentered_profiles", a_nc,
          x ** -2 - h * x ** -3 + h ** 2 * x ** -4)
    check("A_centered_profiles", a_c, y ** -2 + h ** 2 / (4 * y ** 4))
    exp_nc = exponential(-(a_nc - x ** -2), 2).truncate("h", 2)
    exp_c = exponential(-(a_c - y ** -2), 2).truncate("h", 2)
    g_nc_h = integrate_radial_profile((-exp_nc).coefficient("h", 2), "x")
    g_c_h = integrate_radial_profile((-exp_c).coefficient("h", 2), "y")
    g_nc_constant = -F(1, 2) + integrate_radial_profile(
        (-exp_nc).coefficient("h", 1), "x")
    g_c_constant = F(-1)  # The omitted first midpoint contributes -f0(0).
    check("G_noncentered_constant", g_nc_constant, -1)
    check("G_centered_constant", g_c_constant, -1)
    check("G_noncentered_h_integral", g_nc_h, sp / 16)
    check("G_centered_h_integral", g_c_h, sp / 16)

    # Clear denominators before comparing the exact rational finite differences.
    m = symbol("m")
    s2_numerator = ((m + 1) * (2 * m + 1) - 4 * m * (m + 1)
                    + m * (2 * m + 1))
    check("S2_finite_difference_cleared_denominators", s2_numerator, 1,
          "1/(2m)-2/(2m+1)+1/(2m+2)=1/[2m(m+1)(2m+1)]")
    s3_numerator = Poly.lift(0)
    for omitted, weight in enumerate((1, -3, 3, -1)):
        term = Poly.lift(weight)
        for j in range(4):
            if j != omitted:
                term *= 3 * m + j
        s3_numerator += term
    check("S3_finite_difference_cleared_denominators", s3_numerator, 6,
          "1/(3m)-3/(3m+1)+3/(3m+2)-1/(3m+3)"
          "=6/[(3m)(3m+1)(3m+2)(3m+3)]")

    t2_nc = (h / (4 * x ** 3) * geometric_inverse(h / x, 2)
             * geometric_inverse(h / (2 * x), 2)).truncate("h", 2)
    t2_c = (h / (4 * y ** 3)
            * geometric_inverse(-h ** 2 / (4 * y ** 2), 2)).truncate("h", 2)
    check("T2_noncentered_profiles", t2_nc,
          h / (4 * x ** 3) - 3 * h ** 2 / (8 * x ** 4))
    check("T2_centered_h_squared_absent", t2_c.coefficient("h", 2), 0)
    s2_nc_profile = (exp_nc * t2_nc / 2).truncate("h", 2)
    s2_c_profile = (exp_c * t2_c / 2).truncate("h", 2)
    s2_nc_constant = integrate_radial_profile(s2_nc_profile.coefficient("h", 1), "x")
    s2_c_constant = integrate_radial_profile(s2_c_profile.coefficient("h", 1), "y")
    s2_nc_h = integrate_radial_profile(s2_nc_profile.coefficient("h", 2), "x")
    s2_c_h = integrate_radial_profile(s2_c_profile.coefficient("h", 2), "y")
    check("S2_noncentered_constant", s2_nc_constant, F(1, 16))
    check("S2_centered_constant", s2_c_constant, F(1, 16))
    check("S2_noncentered_h_cancellation", s2_nc_h, 0,
          "I6/8 - 3*I4/16 = 0")
    check("S2_centered_h_absence", s2_c_h, 0)

    t3_nc = 6 * h ** 2 / (3 * x) ** 4
    t3_c = 6 * h ** 2 / (3 * y) ** 4
    for j in range(4):
        t3_nc *= geometric_inverse(j * h / (3 * x), 3)
        t3_c *= geometric_inverse((F(j) - F(3, 2)) * h / (3 * y), 3)
        t3_nc = t3_nc.truncate("h", 3)
        t3_c = t3_c.truncate("h", 3)
    check("T3_noncentered_leading_profile", t3_nc.coefficient("h", 2),
          2 / (27 * x ** 4))
    check("T3_centered_leading_profile", t3_c.coefficient("h", 2),
          2 / (27 * y ** 4))
    check("T3_centered_h_cubed_absent", t3_c.coefficient("h", 3), 0)
    nonlinear_nc = (exp_nc * (t3_nc / 3 - t2_nc ** 2 / 8)).coefficient("h", 2)
    nonlinear_c = (exp_c * (t3_c / 3 - t2_c ** 2 / 8)).coefficient("h", 2)
    nonlinear_nc_h = integrate_radial_profile(nonlinear_nc, "x")
    nonlinear_c_h = integrate_radial_profile(nonlinear_c, "y")
    check("nonlinear_noncentered_h_integral", nonlinear_nc_h,
          sp * (F(1, 162) - F(3, 1024)))
    check("nonlinear_centered_h_integral", nonlinear_c_h,
          sp * (F(1, 162) - F(3, 1024)))
    delta_h = f0_integral / 12
    tail_constant = F(-1, 2)
    check("radial_constant_noncentered", g_nc_constant + tail_constant + s2_nc_constant,
          F(-23, 16))
    check("radial_constant_centered", g_c_constant + tail_constant + s2_c_constant,
          F(-23, 16))
    d_nc = (g_nc_h + delta_h + s2_nc_h + nonlinear_nc_h) / sp
    d_c = (g_c_h + delta_h + s2_c_h + nonlinear_c_h) / sp
    check("radial_d_noncentered", d_nc, d)
    check("radial_d_centered", d_c, d)
    check("radial_d_coordinate_agreement", d_nc, d_c)

    beta, s = symbol("beta"), symbol("s")
    m2, m4, m6 = (gaussian_moment(j) for j in (2, 4, 6))
    check("gaussian_second_moment", m2, F(1, 2))
    check("gaussian_fourth_moment", m4, F(3, 4))
    check("gaussian_sixth_moment", m6, F(15, 8))
    saddle_c = m4 - m6 / 2 - beta * m4 - beta * (beta - 1) * m2 / 2
    check("saddle_c_beta_identity", saddle_c,
          -(4 * (beta + 1) ** 2 - 1) / 16)
    c0 = saddle_c.substitute("beta", F(1, 2))
    check("partition_saddle_coefficient", c0, F(-1, 2))
    normalized_c = saddle_c.substitute("beta", s + F(1, 2)) - c0
    check("normalized_saddle_identity", normalized_c, -s * (s + 3) / 4)
    for value, expected in ((F(-1, 2), F(5, 16)), (F(0), F(0)),
                            (F(1, 2), F(-7, 16))):
        check("normalized_saddle_s_" + str(value), normalized_c.substitute("s", value),
              expected)

    # w=x**(-1/2), x=sqrt(n-1/24), r=sqrt(A), u=6**(1/4).
    w, r, u = symbol("w"), symbol("r"), symbol("u")
    ratio_b1 = F(-23, 16) / u
    ratio_b2 = r * (d + F(5, 16) / r ** 2)
    relative_ratio = 1 + ratio_b1 * w + ratio_b2 * w ** 2
    relative_partition = 1 - w ** 2 / (2 * r)
    forward = (relative_ratio * relative_partition).truncate("w", 2)
    b1, b2 = forward.coefficient("w", 1), forward.coefficient("w", 2)
    check("fourth_root_of_six_normalization", u ** 4, 6,
          "u=6^(1/4), so u^4=6")
    check("forward_b1", b1, F(-23, 16) / u,
          "b1=-23/(16*6^(1/4))")
    check("forward_b2", b2, r * d - F(3, 16) / r,
          "b2=sqrt(A)*d-3/(16*sqrt(A))")
    pi = r * u ** 2
    alternate_b2 = (pi / u ** 2) * (d - F(9, 8) / pi ** 2)
    check("forward_b2_pi_form", alternate_b2, b2,
          "b2=(pi/sqrt(6))*(d-9/(8*pi^2)); pi=sqrt(A)*sqrt(6)")
    log_forward = log_one_plus(forward - 1, 2).truncate("w", 2)
    ell1 = log_forward.coefficient("w", 1)
    ell2 = log_forward.coefficient("w", 2)
    check("log_ell1", ell1, b1)
    check("log_ell2", ell2, b2 - b1 ** 2 / 2,
          "ell2=b2-b1^2/2")
    check("log_ell2_explicit", ell2,
          r * d - F(3, 16) / r - F(529, 512) / u ** 2)

    # Pure finite Laurent algebra for the displayed inverse coefficients.
    # This does not prove a root error bound, onset, or an exact ceiling rule.
    B, L1, L2 = symbol("B"), symbol("ell1"), symbol("ell2")
    shift = -(L1 / B) * w - (L2 / B) * w ** 2
    relative_shift = shift * w ** 2
    inverse_residual = (B * shift - F(3, 2) * log_one_plus(relative_shift, 2)
                        + L1 * w * binomial_one_plus(relative_shift, F(-1, 2), 2)
                        + L2 * w ** 2 * geometric_inverse(relative_shift, 2))
    check("inverse_root_cancellation_through_w_squared",
          inverse_residual.truncate("w", 2), 0,
          "x=x0-(ell1/B)*x0^(-1/2)-(ell2/B)*x0^(-1)")
    squared = (w ** -2 + shift) ** 2 + F(1, 24)
    z = w ** -4 - 2 * L1 / B * w ** -1 - 2 * L2 / B + F(1, 24)
    check("inverse_threshold_coefficients", squared.truncate("w", 0), z,
          "Z=x0^2-(2*ell1/B)*x0^(1/2)-(2*ell2/B)+1/24")
    check("inverse_square_exact_residual", squared - z, shift ** 2)

    failures = [item["name"] for item in checks if not item["passed"]]
    if failures:
        raise ValueError("Exact symbolic checks failed: " + ", ".join(failures))

    return {
        "status": "PASS",
        "report": "Report197",
        "sequence": "A373271",
        "arithmetic": "fractions.Fraction; sparse Laurent polynomials; u^4=6",
        "scope": "Finite algebraic checks only; analytic bounds and higher-order claims are not certified",
        "normalizations": {"h": "sqrt(t)", "sqrt_pi": "sqrt(pi)",
                           "r": "sqrt(A), A=pi^2/6", "u": "6^(1/4)",
                           "w_forward": "x^(-1/2), x=sqrt(n-1/24)",
                           "w_inverse": "x0^(-1/2)"},
        "radial_constant": "-23/16",
        "radial_d": str(d),
        "check_count": len(checks),
        "all_passed": all(item["passed"] for item in checks),
        "checks": checks,
    }


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=2, sort_keys=True))
    sys.exit(0 if result["all_passed"] else 1)
