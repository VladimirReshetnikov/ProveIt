"""Optional bounded formal u-series examples over Q[q,z], with q independent.

The finite checks illustrate the separate fixed-run denominator application.
They are not an all-k proof or a claim about a reduced denominator.
"""

from fractions import Fraction
from math import comb, factorial

from run_polynomials import (
    MAX_FILTRATION_K, MAX_N, _poly_add, _poly_multiply, _validate_triangle,
    bounded_integer, egf_run_polynomials, fixed_run_denominator, require,
)


def _scalar(value):
    return {(0, 0): Fraction(value)} if value else {}


def _add(a, b):
    result = a.copy()
    for key, value in b.items():
        result[key] = result.get(key, Fraction(0)) + value
    return {key: value for key, value in result.items() if value}


def _scale(a, value):
    return {key: x * value for key, x in a.items() if x * value}


def _multiply(a, b):
    result = {}
    for (j, ell), v in a.items():
        for (h, m), w in b.items():
            key = (j + h, ell + m)
            result[key] = result.get(key, Fraction(0)) + v * w
    return {key: value for key, value in result.items() if value}


def filtered_run_coefficients(k):
    """Return [u^r]P as {(q exponent,z exponent): Fraction}, 0<=r<=k<=12."""
    bounded_integer(k, "k", 1, MAX_FILTRATION_K)

    def zero():
        return [{} for _ in range(k + 1)]

    def add(a, b):
        return [_add(x, y) for x, y in zip(a, b)]

    def scale(a, value):
        return [_scale(x, value) for x in a]

    def multiply(a, b):
        result = zero()
        for n in range(k + 1):
            for j in range(n + 1):
                result[n] = _add(result[n], _multiply(a[j], b[n - j]))
        return result

    def inverse(a):
        require(set(a[0]) == {(0, 0)}, "u-series inverse requires a scalar constant")
        constant = a[0][0, 0]
        require(constant != 0, "u-series inverse has zero constant")
        result = zero()
        result[0] = _scalar(1 / constant)
        for n in range(1, k + 1):
            for j in range(1, n + 1):
                result[n] = _add(result[n], _multiply(a[j], result[n - j]))
            result[n] = _scale(result[n], -1 / constant)
        return result

    def exponential(a):
        require(not a[0], "u-series exponential requires zero constant")
        result = zero()
        result[0] = _scalar(1)
        for n in range(1, k + 1):
            for j in range(1, n + 1):
                result[n] = _add(result[n], _scale(
                    _multiply(a[j], result[n - j]), Fraction(j, n)))
        return result

    def monomial(a, j, ell):
        return [_multiply(value, {(j, ell): Fraction(1)}) for value in a]

    one = zero()
    one[0] = _scalar(1)
    delta = one.copy()
    delta[1] = _scalar(-2)
    binomial_half = Fraction(1)
    for m in range(1, k // 2 + 1):
        binomial_half *= Fraction(3 - 2 * m, 2 * m)
        for r in range(2 * m, k + 1):
            delta[r] = _add(delta[r], {(m, 0): binomial_half * (-4)**m
                * comb(r - 2, r - 2 * m) * 2**(r - 2 * m)})
    s = zero()
    s[0], s[1] = _scalar(-1), _scalar(2)
    ell_series = one.copy()
    ell_series[1] = {(0, 0): Fraction(-1), (1, 0): Fraction(1)}
    rhs = one.copy()
    rhs[1] = _scalar(-4)
    if k >= 2:
        rhs[2] = {(0, 0): Fraction(4), (1, 0): Fraction(-4)}
    require(multiply(delta, delta) == rhs,
            "delta^2=(1-2u)^2-4u^2*q failed modulo u^(k+1)")
    denominator_inverse = inverse(add(delta, scale(s, -1)))
    exponent = monomial(add(delta, scale(one, -1)), 0, 1)
    a = multiply(monomial(multiply(add(delta, s), denominator_inverse), 1, 0),
                 exponential(exponent))
    four_u = zero()
    four_u[1] = _scalar(4)
    t = multiply(monomial(multiply(four_u, denominator_inverse), 1, 0),
                 exponential(scale(exponent, Fraction(1, 2))))
    result = multiply(multiply(delta, inverse(ell_series)), multiply(
        add(add(one, scale(a, -1)), t), inverse(add(one, a))))
    require(result[0] == _scalar(1), "constant u coefficient is not 1")
    for r in range(1, k + 1):
        require(all(j + ell <= r for j, ell in result[r]),
                f"total-degree filtration failed at k={r}")
        require({key: v for key, v in result[r].items() if key[0] == 0}
                == _scalar(-1), f"q-constant part is not -1 at k={r}")
    return result


def check_filtration(k=5, n=12, rows=None, include_data=False):
    """Check filtered examples against complete EGF rows; construct D_k F_k.

    Optional rows must be a precomputed complete triangle through n. This allows
    the combined CLI to avoid recomputation. All count comparisons are exact.
    """
    bounded_integer(k, "k", 1, MAX_FILTRATION_K)
    bounded_integer(n, "n", 0, MAX_N)
    if rows is None:
        rows = egf_run_polynomials(n)
    _validate_triangle(rows)
    if len(rows) != n + 1:
        raise ValueError("rows must contain exactly n+1 complete polynomials")
    coefficients = filtered_run_coefficients(k)
    comparisons, numerators = 0, {}
    for r in range(1, k + 1):
        for m, row in enumerate(rows):
            value = Fraction(0)
            for (j, ell), c in coefficients[r].items():
                if m >= ell:
                    value += c * Fraction(factorial(m), factorial(m - ell)) * j**(m - ell)
            require(value == (row[r] if r < len(row) else 0),
                    f"filtered-series/EGF coefficient mismatch at k={r}, n={m}")
            comparisons += 1

        def divisor_removed(j, ell):
            result = [Fraction(1)]
            for i in range(1, r + 1):
                exponent = r - i + 1 - (ell + 1 if i == j else 0)
                require(exponent >= 0, "formal term denominator does not divide D_k")
                for _ in range(exponent):
                    result = _poly_multiply(result, [1, -i])
            return result

        denominator = fixed_run_denominator(r)
        numerator = [-x for x in denominator]
        for (j, ell), c in coefficients[r].items():
            if j:
                term = [Fraction(0)] * ell + [
                    c * factorial(ell) * x for x in divisor_removed(j, ell)]
                numerator = _poly_add(numerator, term)
        require(len(numerator) - 1 == r * (r + 1) // 2,
                f"numerator degree mismatch for k={r}")
        require(numerator[-1] == -denominator[-1],
                f"numerator leading coefficient mismatch for k={r}")
        require(all(Fraction(x).denominator == 1 for x in numerator),
                f"nonintegral numerator for k={r}")
        numerators[r] = [int(x) for x in numerator]
    result = {
        "passed": True, "k": k, "n": n,
        "delta_identity_modulus": f"u^{k + 1}",
        "filtration_q_constant_and_numerator_degree_checks": k,
        "coefficient_comparisons": comparisons,
        "numerator_degrees": [r * (r + 1) // 2 for r in range(1, k + 1)],
        "scope": "finite examples; denominator representation, not reduced denominator",
    }
    if include_data:
        result["coefficient_map"] = "entries [j,ell,c] mean c*q^j*z^ell; substitute q=exp(z)"
        result["exponential_polynomials"] = {
            str(r): [[j, ell, str(value)]
                     for (j, ell), value in sorted(coefficients[r].items())]
            for r in range(1, k + 1)}
        result["ordinary_numerators"] = {str(r): value for r, value in numerators.items()}
    return result
