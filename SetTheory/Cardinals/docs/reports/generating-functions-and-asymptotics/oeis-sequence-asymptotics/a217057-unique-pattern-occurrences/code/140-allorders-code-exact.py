"""Report140: bounded exact-arithmetic checks, using only the Python standard library.

Run ``python -I exact.py``.  Importing this module also requires isolated mode.
The output is deterministic JSON: rational numbers are reduced strings, and no
timing, machine, filesystem, or nondeterministic data enters the result.  These
finite checks audit algebra; they do not certify analytic remainder estimates,
infinite sums, numerical constants R5/S5, or a threshold/onset.
"""

# sys is a built-in module.  Check isolation BEFORE any shadowable import.
import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required before any imports\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from math import comb, factorial


class VerificationError(RuntimeError):
    """A mathematical check failed (checks remain active with python -O)."""


def require(condition, label):
    if not condition:
        raise VerificationError(label)


def rational(value):
    return str(Q(value))


def rising(value, length):
    result = Q(1)
    for k in range(length):
        result *= value + k
    return result


def falling(value, length):
    result = Q(1)
    for k in range(length):
        result *= value - k
    return result


def choose(value, length):
    return falling(value, length) / factorial(length)


# Sparse multivariate polynomials.  Exponent tuples, not a symbolic-math
# package, are used for both the Gaussian integrals and symbolic inversion.
def pc(value, variables):
    return {} if not value else {(0,) * variables: Q(value)}


def pv(index, variables):
    powers = [0] * variables
    powers[index] = 1
    return {tuple(powers): Q(1)}


def padd(*polynomials):
    out = {}
    for polynomial in polynomials:
        for key, value in polynomial.items():
            out[key] = out.get(key, Q(0)) + value
            if not out[key]:
                del out[key]
    return out


def pscale(polynomial, scalar):
    return {key: value * scalar for key, value in polynomial.items()
            if value * scalar}


def pmul(left, right):
    out = {}
    for a, v in left.items():
        for b, w in right.items():
            key = tuple(x + y for x, y in zip(a, b))
            out[key] = out.get(key, Q(0)) + v * w
    return {key: value for key, value in out.items() if value}


def ppow(polynomial, exponent, variables):
    out = pc(1, variables)
    for unused in range(exponent):
        out = pmul(out, polynomial)
    return out


def polynomial_json(polynomial, names):
    return {"variables": list(names), "terms": [
        {"powers": list(key), "coefficient": rational(polynomial[key])}
        for key in sorted(polynomial)]}


def gaussian_checks():
    """Integrate after centering four INDEPENDENT N(0,2) coordinates.

    Delta is translation-invariant; the independent scalar mean integrates
    out.  Thus independent one-dimensional even moments suffice, avoiding
    the correlated-coordinate Wick recursion used by the earlier audit.
    """
    variables = 4
    ys = [pv(k, variables) for k in range(variables)]
    mean = pscale(padd(*ys), Q(1, 4))
    theta = [padd(y, pscale(mean, -1)) for y in ys]
    require(not padd(*theta), "centered coordinates sum to zero")
    delta = pc(1, variables)
    for i in range(variables):
        for j in range(i + 1, variables):
            delta = pmul(delta, padd(ys[i], pscale(ys[j], -1)))
    weight = pmul(delta, delta)

    def integrate(poly):
        out = Q(0)
        for powers, coefficient in poly.items():
            if any(power % 2 for power in powers):
                continue
            # E[Y^(2k)] = (2k)! / k! for Y ~ N(0,2).
            value = coefficient
            for power in powers:
                value *= Q(factorial(power), factorial(power // 2))
            out += value
        return out

    norm = integrate(weight)
    require(norm > 0, "positive Gaussian Vandermonde normalization")

    def expectation(poly):
        return integrate(pmul(weight, poly)) / norm

    q2 = padd(*(ppow(t, 2, variables) for t in theta))
    q4 = padd(*(ppow(t, 4, variables) for t in theta))
    moments = {"Q2": expectation(q2),
               "Q2_squared": expectation(pmul(q2, q2)),
               "Q4": expectation(q4)}
    # Independent radial homogeneity check: dimension 3 + degree 12 = 15.
    require(moments["Q2"] == 2 * 15, "radial first moment")
    require(moments["Q2_squared"] == 4 * 15 * 17,
            "radial second moment")
    require(moments["Q4"] == 435, "quartic Gaussian moment")
    correction = padd(pscale(q4, Q(1, 48)),
                      pscale(pmul(q2, q2), Q(-1, 64)),
                      pscale(q2, Q(-1, 3)))
    alpha1 = expectation(correction)
    require(alpha1 == Q(-135, 8), "avoidance alpha1")
    return {"status": "PASS", "method": "centered independent Gaussian moments",
            "largest_total_polynomial_degree": 16,
            "normalizing_polynomial_moment": rational(norm),
            "moments": {key: rational(value) for key, value in moments.items()},
            "alpha1": rational(alpha1)}


def partitions(size, rows=4, maximum=None):
    if size == 0:
        yield ()
        return
    if rows == 0:
        return
    maximum = size if maximum is None else min(maximum, size)
    for first in range(maximum, 0, -1):
        for tail in partitions(size - first, rows - 1, first):
            yield (first,) + tail


def cells(outer, inner):
    if len(inner) > len(outer) or any(
            value > outer[i] for i, value in enumerate(inner)):
        return None
    return tuple((r, c) for r, length in enumerate(outer)
                 for c in range(inner[r] if r < len(inner) else 0, length))


@lru_cache(None)
def standard_skew_count(outer, inner):
    """Count increasing fillings as linear extensions of the cell poset."""
    shape = cells(outer, inner)
    if shape is None:
        return 0
    indexes = {cell: i for i, cell in enumerate(shape)}
    predecessors = []
    for r, c in shape:
        mask = 0
        for predecessor in ((r - 1, c), (r, c - 1)):
            if predecessor in indexes:
                mask |= 1 << indexes[predecessor]
        predecessors.append(mask)

    @lru_cache(None)
    def extensions(mask):
        if mask == (1 << len(shape)) - 1:
            return 1
        total = 0
        for i, previous in enumerate(predecessors):
            if not mask & (1 << i) and previous & mask == previous:
                total += extensions(mask | (1 << i))
        return total

    return extensions(0)


@lru_cache(None)
def skew_weights(outer, inner, alphabet=4):
    """Enumerate skew SSYT directly: weak rows and strict columns."""
    shape = cells(outer, inner)
    if shape is None:
        return ()
    filling, counts, answer = {}, [0] * alphabet, {}

    def visit(index):
        if index == len(shape):
            key = tuple(counts)
            answer[key] = answer.get(key, 0) + 1
            return
        r, c = shape[index]
        minimum = max(filling.get((r, c - 1), 1),
                      filling.get((r - 1, c), 0) + 1)
        for value in range(minimum, alphabet + 1):
            filling[r, c] = value
            counts[value - 1] += 1
            visit(index + 1)
            counts[value - 1] -= 1
        filling.pop((r, c), None)

    visit(0)
    return tuple(sorted(answer.items()))


def weyl_dimension(shape):
    padded = shape + (0,) * (4 - len(shape))
    value = Q(1)
    for i in range(4):
        for j in range(i + 1, 4):
            value *= Q(padded[i] - padded[j] + j - i, j - i)
    return value


def character_functionals(weights):
    dimension = sum(weights.values())
    if not weights:
        return Q(0), Q(0), Q(0)
    degrees = {sum(key) for key in weights}
    require(len(degrees) == 1, "character is homogeneous")
    degree = next(iter(degrees))
    variance = sum(multiplicity * (key[0] ** 2 - key[0] * key[1])
                   for key, multiplicity in weights.items())
    jvalue = Q(15, 4) * (4 * variance - degree * dimension)
    return Q(dimension), Q(variance), jvalue


def transpose(shape):
    return tuple(sum(value > col for value in shape)
                 for col in range(max(shape, default=0)))


def boundary_character(P, R, tau):
    out = {}
    for shape in partitions(P, rows=2):
        multiplicity = standard_skew_count(shape, (R,))
        if multiplicity:
            for weight, count in skew_weights(shape, tau):
                out[weight] = out.get(weight, 0) + multiplicity * count
    return out


def character_checks():
    checked = 0
    for size in range(7):
        for shape in partitions(size):
            weights = dict(skew_weights(shape, ()))
            dimension, variance, jvalue = character_functionals(weights)
            require(dimension == weyl_dimension(shape), "SSYT/Weyl dimension")
            kappa = sum(value * (value - 2 * row + 1)
                        for row, value in enumerate(shape, start=1))
            require(jvalue == dimension * (kappa - Q(size * (size - 1), 4)),
                    "derivative/Casimir J identity")
            # Independently inspect full coordinate permutation symmetry.
            for weight, count in weights.items():
                for permuted in set(permutations(weight)):
                    require(weights.get(permuted, 0) == count,
                            "SSYT character weight symmetry")
            checked += 1

    taus = ((), (1,), (2,), (1, 1), (2, 1), (2, 2))
    examples = []
    for parameters in ((0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0)):
        i2, i3, j2, j3 = parameters
        P, R, S, T = i2 + i3 + 1, i3 + 1, j2 + j3 + 1, j2 + 1
        total_h, total_b, rows = Q(0), Q(0), []
        for tau in taus:
            size = sum(tau)
            dF, unused, jF = character_functionals(boundary_character(P, R, tau))
            dG, unused, jG = character_functionals(
                boundary_character(S, T, transpose(tau)))
            ht = (-1) ** size * dF * dG
            bt = (-1) ** size * (
                -Q(15, 2) * (2 - size) * dF * dG - jF * dG - dF * jG)
            total_h += ht
            total_b += bt
            rows.append({"tau": list(tau), "D_F": rational(dF),
                         "J_F": rational(jF), "D_G": rational(dG),
                         "J_G": rational(jG), "h_summand": rational(ht),
                         "B_summand": rational(bt)})
        scale = Q(256, 4 ** (P + S))
        hvalue, bvalue = scale * total_h, scale * total_b
        record = {"boundary": list(parameters), "h": rational(hvalue),
                  "B": rational(bvalue), "scale": rational(scale),
                  "six_character_terms": rows}
        if parameters[1] == 0:
            # H_s=A_(s+2)-k*A_(s+1); normalize BEFORE expanding.
            k = 1 + parameters[0]
            shifted_h = Q(16 ** 2 - k * 16)
            shifted_b = -Q(15, 2) * (2 * 16 ** 2 - k * 16)
            require((hvalue, bvalue) == (shifted_h, shifted_b),
                    "six-character versus shifted-avoidance half check")
            record["independent_shifted_avoidance"] = {
                "A_s_plus_1_multiplier": -k, "h": rational(shifted_h),
                "B": rational(shifted_b)}
        else:
            # For G_(2,2)=s_(2), G_(1,1)=s_(1), direct monomial
            # formulas provide a second character construction.
            square = {}
            for a in range(4):
                for b in range(a, 4):
                    powers = [0] * 4
                    powers[a] += 1
                    powers[b] += 1
                    square[tuple(powers)] = 1
            require(boundary_character(2, 2, ()) == square,
                    "third half complete symmetric quadratic character")
            require((hvalue, bvalue) == (144, -2520), "third half h/B")
        examples.append(record)
    require([(entry["h"], entry["B"]) for entry in examples] ==
            [("240", "-3720"), ("224", "-3600"), ("144", "-2520")],
            "all three published half values")
    return {"status": "PASS", "partition_size_range": [0, 6],
            "maximum_rows": 4, "characters_checked": checked,
            "method": "direct standard/skew semistandard tableau enumeration",
            "half_examples": examples}


# Scalar truncated power-series arithmetic, with exact rational coefficients.
def s_add(left, right, order):
    return [(left[i] if i < len(left) else Q(0)) +
            (right[i] if i < len(right) else Q(0)) for i in range(order + 1)]


def s_scale(series, value, order):
    return [(series[i] if i < len(series) else Q(0)) * value
            for i in range(order + 1)]


def s_mul(left, right, order):
    out = [Q(0)] * (order + 1)
    for i, a in enumerate(left[:order + 1]):
        for j, b in enumerate(right[:order + 1 - i]):
            out[i + j] += a * b
    return out


def s_power_unit(series, exponent, order):
    require(series[0] == 1, "unit series for generalized power")
    u = list(series[:order + 1]) + [Q(0)] * max(0, order + 1 - len(series))
    u[0] = Q(0)
    out, power = [Q(0)] * (order + 1), [Q(1)] + [Q(0)] * order
    for k in range(order + 1):
        out = s_add(out, s_scale(power, choose(exponent, k), order), order)
        power = s_mul(power, u, order)
    return out


def s_compose(series, argument, order):
    require(argument[0] == 0, "zero constant in composition argument")
    out, power = [Q(0)] * (order + 1), [Q(1)] + [Q(0)] * order
    for coefficient in series[:order + 1]:
        out = s_add(out, s_scale(power, coefficient, order), order)
        power = s_mul(power, argument, order)
    return out


def gamma_recurrence_residual(x, coefficients, order):
    # In t=1/n, q(n+1)=(n-x)/(n+1)q(n) becomes
    # (1+t)^(-x) G(t/(1+t)) = (1-x*t) G(t).
    unit = [Q(1), Q(1)]
    reciprocal = s_power_unit(unit, -1, order)
    argument = [Q(0)] + reciprocal[:order]
    left = s_mul(s_power_unit(unit, -x, order),
                 s_compose(coefficients, argument, order), order)
    right = s_mul([Q(1), -x], coefficients, order)
    return s_add(left, s_scale(right, -1, order), order)


@lru_cache(None)
def gamma_coefficients(x, order):
    """Solve the exact recurrence by coefficient extraction and slope tests.

    No closed formula for g_h or precomputed Bernoulli data enters this path.
    """
    coefficients = [Q(1)]
    for degree in range(1, order + 1):
        zero = gamma_recurrence_residual(x, coefficients + [Q(0)], degree + 1)
        one = gamma_recurrence_residual(x, coefficients + [Q(1)], degree + 1)
        slope = one[degree + 1] - zero[degree + 1]
        require(slope != 0, "nonzero triangular recurrence slope")
        coefficients.append(-zero[degree + 1] / slope)
    residual = gamma_recurrence_residual(x, coefficients, order + 1)
    require(all(value == 0 for value in residual), "gamma exact recurrence residual")
    return tuple(coefficients)


def bernoulli_numbers(order):
    values = [Q(1)]
    for n in range(1, order + 1):
        values.append(-sum(Q(comb(n + 1, k)) * values[k]
                           for k in range(n)) / (n + 1))
    return values


def gamma_bernoulli(x, order):
    numbers = bernoulli_numbers(order + 1)

    def polynomial(n, value):
        return sum(Q(comb(n, k)) * numbers[k] * value ** (n - k)
                   for k in range(n + 1))

    logarithm = [Q(0)] + [
        Q((-1) ** (r + 1), r * (r + 1)) *
        (polynomial(r + 1, -x) - polynomial(r + 1, Q(1)))
        for r in range(1, order + 1)]
    # Direct exp(logarithm)=sum log^k/k!, independent of the q recurrence.
    out, power = [Q(0)] * (order + 1), [Q(1)] + [Q(0)] * order
    for k in range(order + 1):
        out = s_add(out, s_scale(power, Q(1, factorial(k)), order), order)
        power = s_mul(power, logarithm, order)
    return tuple(out)


def gamma_checks():
    order, results = 12, []
    for j in range(13):
        x = Q(13, 2) + j
        computed = gamma_coefficients(x, order)
        require(computed == gamma_bernoulli(x, order),
                "recurrence/Bernoulli gamma coefficients")
        require(computed[1] == x * (x + 1) / 2, "g1 formula")
        require(computed[2] == x * (x + 1) * (x + 2) * (3 * x + 1) / 24,
                "g2 formula")
        results.append({"j": j, "x": rational(x),
                        "coefficients": [rational(c) for c in computed]})
    return {"status": "PASS", "model_index_range": [0, 12],
            "coefficient_degree_range": [0, 12], "coefficient_comparisons": 169,
            "methods": ["exact recurrence coefficient solving",
                        "Bernoulli polynomial exponential"],
            "models": results}


@lru_cache(None)
def q_model(x, n):
    if n < 0:
        return Q(0)
    return (-1) ** n * choose(x, n)


def binomial_checks():
    alpha, pairs, comparisons, tail_zeroes = Q(13, 2), 0, 0, 0
    for j in range(7):
        for k in range(7):
            degree = 13 + j + k
            pairs += 1
            for n in range(41):
                value = sum(q_model(alpha + j, s) * q_model(alpha + k, n - s)
                            for s in range(n + 1))
                polynomial_coefficient = (Q((-1) ** n * comb(degree, n))
                                          if n <= degree else Q(0))
                require(value == polynomial_coefficient, "exact model product")
                comparisons += 1
                if n > degree:
                    require(value == 0, "model-model tail vanishes")
                    tail_zeroes += 1
    recurrence_checks = 0
    for j in range(13):
        x = alpha + j
        for n in range(40):
            require((n + 1) * q_model(x, n + 1) == (n - x) * q_model(x, n),
                    "direct binomial coefficients satisfy recurrence")
            recurrence_checks += 1
    return {"status": "PASS", "j_k_range": [0, 6], "n_range": [0, 40],
            "model_pairs": pairs, "coefficient_comparisons": comparisons,
            "exact_zero_coefficients_beyond_polynomial_degree": tail_zeroes,
            "binomial_recurrence_comparisons": recurrence_checks,
            "recurrence_j_range": [0, 12], "recurrence_n_range": [0, 39]}


def discrete_taylor_checks():
    comparisons = 0
    for j in range(4):
        x = Q(13, 2) + j
        for n in range(25):
            for s in range(n + 1):
                for d in range(6):
                    main = sum((-1) ** ell * comb(s, ell) * q_model(x + ell, n)
                               for ell in range(min(d, s) + 1))
                    remainder = (-1) ** (d + 1) * sum(
                        comb(s - 1 - k, d) * q_model(x + d + 1, n - k)
                        for k in range(max(0, s - d)))
                    require(q_model(x, n - s) == main + remainder,
                            "exact discrete Taylor with finite remainder")
                    comparisons += 1
    return {"status": "PASS", "j_range": [0, 3], "n_range": [0, 24],
            "s_range": "0..n", "d_range": [0, 5],
            "exact_remainder_identity_comparisons": comparisons}


def mat_mul(left, right):
    n = len(left)
    return [[sum(left[i][k] * right[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]


def triangular_checks():
    order, alpha, p = 12, Q(13, 2), Q(15, 2)
    n = order + 1
    identity = [[Q(i == j) for j in range(n)] for i in range(n)]
    G = [[gamma_coefficients(alpha + j, order)[i - j] if i >= j else Q(0)
          for j in range(n)] for i in range(n)]
    negative_nilpotent = [[identity[i][j] - G[i][j] for j in range(n)]
                         for i in range(n)]
    # Inverse by a finite geometric series in a strictly lower triangular
    # matrix, rather than copying the coefficient-by-coefficient recurrence.
    inverse, power = [row[:] for row in identity], [row[:] for row in identity]
    for unused in range(1, n):
        power = mat_mul(power, negative_nilpotent)
        inverse = [[inverse[i][j] + power[i][j] for j in range(n)]
                   for i in range(n)]
    require(mat_mul(power, negative_nilpotent) == [[Q(0)] * n for unused in range(n)],
            "triangular nilpotence")
    require(mat_mul(G, inverse) == identity, "right triangular inverse")
    require(mat_mul(inverse, G) == identity, "left triangular inverse")
    require(inverse[1][0] == Q(-195, 8), "T1 coefficient")

    # Polynomial in shift s for each abstract input coefficient U_i.
    # First compute falling-factorial polynomials by multiplication.
    falls = [[Q(1)]]
    for ell in range(1, n):
        falls.append(s_mul(falls[-1], [Q(-(ell - 1)), Q(1)], ell))
    compared = 0
    for m in range(n):
        left = [[Q(0)] * n for unused in range(n)]
        for j in range(m + 1):
            for ell in range(m - j + 1):
                h = m - j - ell
                scalar = (gamma_coefficients(alpha + j + ell, order)[h] *
                          rising(p + j, ell) / factorial(ell))
                for i in range(j + 1):
                    for degree, coeff in enumerate(falls[ell]):
                        left[i][degree] += inverse[j][i] * scalar * coeff
        right = [[Q(0)] * n for unused in range(n)]
        for i in range(m + 1):
            right[i][m - i] = rising(p + i, m - i) / factorial(m - i)
        for i in range(m + 1):
            for degree in range(m + 1):
                require(left[i][degree] == right[i][degree],
                        "binomial and inverse-power shifted coefficient identity")
                compared += 1
    return {"status": "PASS", "orders": [0, order],
            "matrix_dimension": n, "matrix_inverse_entries_checked": 2 * n * n,
            "shift_polynomial_coefficients_compared": compared,
            "T1_U0_coefficient": rational(inverse[1][0]),
            "first_direct_convolution_coefficients": {
                "B0_U0_m0": "2", "B1_U1_m0": "2", "B1_U0_m1": rational(2 * p),
                "B2_U2_m0": "2", "B2_U1_m1": rational(2 * (p + 1)),
                "B2_U0_m2": rational(p * (p + 1))}}


def stirling_table(order):
    table = [[0] * (order + 1) for unused in range(order + 1)]
    table[0][0] = 1
    for n in range(1, order + 1):
        for k in range(1, n + 1):
            table[n][k] = table[n - 1][k - 1] + k * table[n - 1][k]
    return table


def moment_checks():
    order, table = 12, stirling_table(12)
    sequence = [Q((-1) ** n * (n * n + 3), (n + 1) * (n + 2))
                for n in range(31)]
    # This finite signed test sequence has no positivity assumption.
    mu = [sum(falling(n, k) * value for n, value in enumerate(sequence))
          for k in range(order + 1)]
    powers = [sum(Q(n) ** ell * value for n, value in enumerate(sequence))
              for ell in range(order + 1)]
    count = 0
    for ell in range(order + 1):
        transformed = sum(table[ell][k] * mu[k] for k in range(ell + 1))
        require(transformed == powers[ell], "finite moment Stirling transform")
        for n in range(31):
            require(Q(n) ** ell == sum(table[ell][k] * falling(n, k)
                                      for k in range(ell + 1)),
                    "power/falling polynomial identity")
            count += 1

    # Exact partial sums, rather than approximating an infinite zero moment:
    # sum_{n<=N} n^[l] q_x(n) = (-1)^l x^[l] q_(x-l-1)(N-l).
    partial_count = 0
    for j in range(13):
        x = Q(13, 2) + j
        for ell in range(13):
            if x <= ell:
                continue
            partial = Q(0)
            for N in range(25):
                partial += falling(N, ell) * q_model(x, N)
                rhs = (-1) ** ell * falling(x, ell) * q_model(x - ell - 1, N - ell)
                require(partial == rhs, "exact model falling moment partial sum")
                partial_count += 1
    require(Q(6) - Q(15, 2) < -1 and Q(7) - Q(15, 2) > -1,
            "ordinary moment summability threshold")
    residual_checks = []
    for ell in range(7, 13):
        L = ell - 7
        weighted_exponent = ell - Q(15, 2) - L - 1
        require(weighted_exponent == Q(-3, 2), "regularized weighted tail exponent")
        residual_checks.append({"moment_order": ell, "last_subtracted_model": L,
                                "weighted_tail_exponent": rational(weighted_exponent)})
    return {"status": "PASS", "moment_orders": [0, order],
            "finite_sequence_support": [0, 30], "power_identity_comparisons": count,
            "moment_transform_comparisons": order + 1,
            "model_partial_sum_comparisons": partial_count,
            "model_partial_sum_j_range": [0, 12], "model_partial_sum_l_range": [0, 12],
            "model_partial_sum_N_range": [0, 24], "model_partial_sum_condition": "13/2+j>l",
            "first_required_subtraction_order": 7,
            "regularization_exponent_checks": residual_checks,
            "infinite_moments_numerically_approximated": False}


def s_divide(numerator, denominator, order):
    require(denominator[0] != 0, "series denominator nonzero")
    quotient = []
    for n in range(order + 1):
        convolution = sum(denominator[k] * quotient[n - k]
                          for k in range(1, min(n, len(denominator) - 1) + 1))
        quotient.append(((numerator[n] if n < len(numerator) else Q(0)) - convolution)
                        / denominator[0])
    return quotient


def ratio_shift_checks():
    p, order, shift = Q(15, 2), 12, Q(5)
    samples, comparisons = [], 0
    for sample in range(3):
        c = [Q((-1) ** (n + sample) * (n + sample + 2), n + 1)
             for n in range(order + 1)]
        avoidance = [Q(1), Q(-135, 8)] + [
            Q((-1) ** (n + sample) * (n + 1), n + sample + 2)
            for n in range(2, order + 1)]
        unit = [Q(1), -shift]
        inverse = s_power_unit(unit, -1, order)
        argument = [Q(0)] + inverse[:order]
        shifted = s_scale(s_mul(s_power_unit(unit, -p, order),
                               s_compose(c, argument, order), order),
                          Q(1, 16 ** 5), order)
        explicit = [Q(1, 16 ** 5) * sum(
            c[m] * rising(p + m, r - m) * shift ** (r - m) / factorial(r - m)
            for m in range(r + 1)) for r in range(order + 1)]
        require(shifted == explicit, "fixed shift substitution/coefficient formula")
        ratio = s_divide(shifted, avoidance, order)
        require(s_mul(ratio, avoidance, order) == shifted, "ratio division product check")
        inverse_avoidance = s_power_unit(avoidance, -1, order)
        require(s_mul(shifted, inverse_avoidance, order) == ratio,
                "ratio geometric inverse versus triangular division")
        comparisons += 3 * (order + 1)

        # Two independent formal logarithm constructions: powers of A-1
        # and integration of A'/A.
        u = avoidance[:]
        u[0] = Q(0)
        log_by_powers, power = [Q(0)] * (order + 1), [Q(1)] + [Q(0)] * order
        for k in range(1, order + 1):
            power = s_mul(power, u, order)
            log_by_powers = s_add(log_by_powers,
                                  s_scale(power, Q((-1) ** (k + 1), k), order), order)
        derivative = [(n + 1) * avoidance[n + 1] for n in range(order)]
        derivative_ratio = s_divide(derivative, avoidance, order - 1)
        log_by_derivative = [Q(0)] + [derivative_ratio[n - 1] / n
                                     for n in range(1, order + 1)]
        require(log_by_powers == log_by_derivative, "logarithm power/derivative identity")
        comparisons += order + 1
        samples.append({"sample": sample, "shifted_coefficients":
                        [rational(x) for x in shifted], "ratio_coefficients":
                        [rational(x) for x in ratio]})

    # Symbolic first-order cancellation, with no numerical h, B, or moments.
    nv = 5
    h, B, m0, m1, a1 = [pv(i, nv) for i in range(nv)]
    c0 = pscale(pmul(h, m0), 2)
    c1 = padd(pscale(pmul(padd(pmul(a1, h), B), m0), 2),
               pscale(pmul(h, m1), 2 * p))
    b0 = pscale(c0, Q(1, 16 ** 5))
    b1 = pscale(padd(c1, pscale(c0, p * shift)), Q(1, 16 ** 5))
    r1 = padd(b1, pscale(pmul(a1, b0), -1))
    expected = pscale(padd(pmul(B, m0), pscale(pmul(h, m1), p),
                             pscale(pmul(h, m0), p * shift)), Q(2, 16 ** 5))
    require(r1 == expected, "symbolic alpha1 cancellation in first ratio coefficient")
    require(all(powers[4] == 0 for powers in r1), "alpha1 disappears from r1")
    return {"status": "PASS", "orders": [0, order], "shift": rational(shift),
            "exponential_factor": rational(Q(1, 16 ** 5)), "samples": samples,
            "sample_coefficient_comparisons": comparisons,
            "symbolic_first_ratio_correction": polynomial_json(r1, ("h", "B", "m0", "m1", "alpha1")),
            "alpha1_cancellation_verified": True}


# Polynomial-coefficient series for symbolic inverse reversion.
def ps_add(left, right, order):
    return [padd(left[i] if i < len(left) else {}, right[i] if i < len(right) else {})
            for i in range(order + 1)]


def ps_mul(left, right, order):
    out = [{} for unused in range(order + 1)]
    for i, a in enumerate(left[:order + 1]):
        for j, b in enumerate(right[:order + 1 - i]):
            out[i + j] = padd(out[i + j], pmul(a, b))
    return out


def ps_power_unit(series, exponent, order, nv):
    require(series[0] == pc(1, nv), "polynomial unit series")
    u = series[:] + [{} for unused in range(max(0, order + 1 - len(series)))]
    u[0] = {}
    out, power = [{} for unused in range(order + 1)], [pc(1, nv)]
    for k in range(order + 1):
        out = ps_add(out, [pscale(poly, choose(exponent, k)) for poly in power], order)
        power = ps_mul(power, u, order)
    return out


def inverse_residual(corrections, order):
    # y=L+a+sum(P_j/L^j), a=p*log(L)-d.  The transformed residual is
    # sum(P_j*t^j)-p*log(y/L)+sum(e_j*t^j*(y/L)^(-j)), t=1/L.
    nv = 6
    a, p, e1, e2, e3, e4 = [pv(i, nv) for i in range(nv)]
    es = (None, e1, e2, e3, e4)
    unit = [pc(1, nv), a] + corrections
    u = unit[:]
    u[0] = {}
    logarithm, power = [{} for unused in range(order + 1)], [pc(1, nv)]
    for k in range(1, order + 1):
        power = ps_mul(power, u, order)
        logarithm = ps_add(logarithm,
                           [pscale(poly, Q((-1) ** (k + 1), k)) for poly in power], order)
    residual = ps_add([{}] + corrections,
                      [pscale(pmul(p, poly), -1) for poly in logarithm], order)
    for j in range(1, min(order, 4) + 1):
        reciprocal = ps_power_unit(unit, -j, order - j, nv)
        term = [{} for unused in range(j)] + [pmul(es[j], poly) for poly in reciprocal]
        residual = ps_add(residual, term, order)
    return residual


def inverse_checks():
    nv, order = 6, 4
    a, p, e1, e2, e3, e4 = [pv(i, nv) for i in range(nv)]
    corrections = []
    for j in range(1, order + 1):
        residual = inverse_residual(corrections, j)
        require(all(not poly for poly in residual[:j]),
                "previous inverse coefficients already vanish")
        corrections.append(pscale(residual[j], -1))
    full_residual = inverse_residual(corrections, order)
    require(all(not poly for poly in full_residual), "symbolic inverse reversion residual")
    P1 = padd(pmul(p, a), pscale(e1, -1))
    P2 = padd(pscale(pmul(p, ppow(a, 2, nv)), Q(-1, 2)),
               pmul(padd(ppow(p, 2, nv), e1), a),
               pscale(pmul(p, e1), -1), pscale(e2, -1))
    require(corrections[0] == P1 and corrections[1] == P2,
            "published first two inverse polynomials")
    # a=p*z-d: checking a-degree establishes the claimed log-polynomial bound.
    degrees = [max((powers[0] for powers in poly), default=0) for poly in corrections]
    require(all(degree <= j for j, degree in enumerate(degrees, start=1)),
            "inverse logarithm-polynomial degree bounds")
    return {"status": "PASS", "verified_orders": order,
            "symbolic_variables": ["a", "p", "e1", "e2", "e3", "e4"],
            "residual_coefficients_through_order": ["0"] * (order + 1),
            "a_degrees": degrees,
            "polynomials": [polynomial_json(poly, ("a", "p", "e1", "e2", "e3", "e4"))
                            for poly in corrections],
            "integer_threshold_rounding_certified": False}


def run():
    """Return all bounded exact checks; any failed check raises, also under -O."""
    results = {"schema": "report140-independent-exact-v1",
               "arithmetic": "standard-library fractions.Fraction",
               "scope": "finite algebra checks, not analytic remainder certification",
               "gaussian": gaussian_checks(),
               "characters_and_half_corrections": character_checks(),
               "gamma_ratio": gamma_checks(),
               "binomial_product": binomial_checks(),
               "discrete_taylor": discrete_taylor_checks(),
               "triangular_matching": triangular_checks(),
               "moment_stirling": moment_checks(),
               "ratio_and_shift": ratio_shift_checks(),
               "inverse_reversion": inverse_checks()}
    require(all(result["status"] == "PASS" for result in results.values()
                if isinstance(result, dict) and "status" in result), "all sections passed")
    results["status"] = "PASS"
    return results


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True, allow_nan=False))
