"""Exact algebraic checks for the separately approved crossover supplement.

Only nonnegative integer outer exponents are used by the coefficient engines.
These routines check rational identities, not analytic uniform remainders.
"""
from fractions import Fraction as F
from math import factorial
import diagonal_euler as de

Q_POLYNOMIALS = ((F(0), F(-1), F(2)), (F(0), F(1), F(2)), (F(0), F(-1), F(2)))
E_POLYNOMIALS = ((F(0), F(-1, 6), F(3, 2), F(-10, 3), F(2)),
                 (F(0), F(-1, 6), F(-1, 2), F(2, 3), F(2)),
                 (F(0), F(-1, 6), F(3, 2), F(-10, 3), F(2)))
PURE_INDICES = (0, 2, 1)
PURE_AMPLITUDES = (F(1), F(3, 2), F(1))


def h_coefficient(k):
    """H_k=[u^k] exp(u+u^2), as a finite exact factorial sum."""
    de.integer(k, "k")
    return sum((F(1, factorial(k - 2 * b) * factorial(b))
                for b in range(k // 2 + 1)), F(0))


def h_coefficients(order):
    """Independent H recurrence from H'(u)=(1+2u)H(u)."""
    de.integer(order, "order")
    values = [F(1)]
    for k in range(order):
        values.append((values[k] + (2 * values[k - 1] if k else 0)) / (k + 1))
    return tuple(values)


def psi_coefficients(r, order):
    de.residue(r)
    de.integer(order, "order")
    return tuple(h_coefficient(PURE_INDICES[r] + 3 * h) / PURE_AMPLITUDES[r]
                 for h in range(order + 1))


def p_factor(m, ell):
    """P_ell(m), including its exact coefficient-cutoff convention."""
    de.integer(m, "m", 1)
    de.integer(ell, "ell")
    return de.falling(m, ell) / m ** ell if ell <= m else F(0)


def polynomial_multiply(left, right):
    """Ascending-order exact rational polynomial multiplication."""
    if type(left) is not tuple or type(right) is not tuple or not left or not right:
        raise TypeError("polynomials must be nonempty tuples")
    left = tuple(de.rational(c, "polynomial coefficient") for c in left)
    right = tuple(de.rational(c, "polynomial coefficient") for c in right)
    result = [F(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return tuple(result)


def polynomial_value(coefficients, x):
    if type(coefficients) is not tuple or not coefficients:
        raise TypeError("polynomial must be a nonempty tuple")
    x = de.rational(x, "x")
    value = F(0)
    for coefficient in reversed(coefficients):
        value = value * x + de.rational(coefficient, "coefficient")
    return value


def p_inverse_m_polynomial(ell):
    """Exact coefficients of product_(i=0)^(ell-1)(1-i/m) in powers of 1/m."""
    de.integer(ell, "ell")
    result = (F(1),)
    for i in range(ell):
        result = polynomial_multiply(result, (F(1), F(-i)))
    while len(result) > 1 and result[-1] == 0:
        result = result[:-1]
    return result


def derived_q_e_polynomials(r):
    """Substitute ell=2h+[r=1] in s1=ell(ell-1)/2 and e2 exactly."""
    de.residue(r)
    shift = int(r == 1)
    ell = (F(shift), F(2))
    ell_minus_1 = (F(shift - 1), F(2))
    ell_minus_2 = (F(shift - 2), F(2))
    three_ell_minus_1 = (F(3 * shift - 1), F(6))
    q = tuple(c / 2 for c in polynomial_multiply(ell, ell_minus_1))
    e = polynomial_multiply(polynomial_multiply(ell, ell_minus_1),
                            polynomial_multiply(ell_minus_2, three_ell_minus_1))
    return q, tuple(c / 24 for c in e)


def rational_exponent_inequalities():
    """Exact inequalities equivalent to 2<delta<3 and eta>3; no logarithms."""
    q = F(8, 9)
    rho_squared = F(25, 32)
    nu_squared = F(9, 16)
    return {
        "delta_upper": (q ** 3, rho_squared),
        "delta_lower": (rho_squared, q ** 2),
        "eta_lower": (nu_squared, q ** 3),
    }


def exact_crossover_certificate():
    """Raise explicit failures on any inconsistent algebraic ingredient."""
    from certificate import equal, require
    equal(h_coefficients(24), tuple(h_coefficient(k) for k in range(25)),
          "independent H recurrence and factorial sum")
    expected = ((F(1), F(7, 6), F(331, 720)),
                (F(1), F(9, 20), F(1979, 20160)),
                (F(1), F(25, 24), F(1303, 5040)))
    for r in range(3):
        equal(psi_coefficients(r, 2), expected[r], "first crossover coefficients")
        equal(derived_q_e_polynomials(r), (Q_POLYNOMIALS[r], E_POLYNOMIALS[r]),
              "symbolic Q/E polynomial identities")
    for ell in range(25):
        p = p_inverse_m_polynomial(ell)
        coefficient_1 = p[1] if len(p) > 1 else F(0)
        coefficient_2 = p[2] if len(p) > 2 else F(0)
        equal(-coefficient_1, F(ell * (ell - 1), 2), "P first finite-size coefficient")
        equal(coefficient_2, F(ell * (ell - 1) * (ell - 2) * (3 * ell - 1), 24),
              "P second finite-size coefficient")
    inequalities = rational_exponent_inequalities()
    for name, (left, right) in inequalities.items():
        require(left < right, f"cleared rational inequality: {name}")
    cleared = {
        # Reduced integer cross-products after cancelling their common gcd.
        "delta_upper": (16384, 18225),
        "delta_lower": (2025, 2048),
        "eta_lower": (6561, 8192),
    }
    from math import gcd
    proof_rows = []
    for name, (left, right) in inequalities.items():
        a, b = left.numerator * right.denominator, right.numerator * left.denominator
        common = gcd(a, b)
        equal((a // common, b // common), cleared[name], "cleared-denominator fixture")
        proof_rows.append({"name": name, "left": left, "right": right,
                           "cleared_left": a // common, "cleared_right": b // common})
    return {
        "scope": "Exact finite identities and exponent inequalities only; uniform asymptotic estimates require the analytic proof.",
        "H_k0_to_k12": h_coefficients(12),
        "psi_z0_to_z6": [{"residue": r, "coefficients": psi_coefficients(r, 6)} for r in range(3)],
        "Q_E_polynomial_coefficients_ascending": [
            {"residue": r, "Q": Q_POLYNOMIALS[r], "E": E_POLYNOMIALS[r]} for r in range(3)],
        "P_finite_size_coefficients_checked_ell_inclusive": [0, 24],
        "exponent_inequalities": proof_rows,
        "conclusions": ["2 < delta < 3", "eta > 3"],
    }
