"""Exact counts and parity-resolved saddle expansions for weighted lattice bridges.

Numerical saddle evaluations use mpmath; they are not interval certificates.
The explicit analytic error envelope is proved in the accompanying article.
"""
from fractions import Fraction
from math import comb, factorial
import mpmath as mp


def axis_coefficients(dimension, order):
    """Return (k!)**2 [t**k] I0(2 sqrt(t))**dimension, as integers."""
    if dimension < 0 or int(dimension) != dimension:
        raise ValueError("dimension must be a nonnegative integer")
    q = [1]
    for n in range(1, order + 1):
        total = sum(((dimension + 1) * k - n) * comb(n, k)**2 * q[n-k]
                    for k in range(1, n + 1))
        quotient, remainder = divmod(total, n)
        if remainder:
            raise ArithmeticError("coefficient recurrence lost integrality")
        q.append(quotient)
    return q


def exact_count(length, dimension, idle=1):
    """Exact rational weighted count for an integer/rational idle activity."""
    idle = Fraction(idle)
    q = axis_coefficients(dimension, length // 2)
    return sum(Fraction(comb(length, 2*k) * comb(2*k, k) * q[k])
               * idle**(length-2*k) for k in range(length//2 + 1))


def coefficient_convolution(left, right, order):
    out = [Fraction(0) for _ in range(order+1)]
    for i, a in enumerate(left[:order+1]):
        for j, b in enumerate(right[:order+1-i]):
            out[i+j] += a*b
    return out


def exact_anisotropic(length, pair_weights, idle=1):
    """Independent rational convolution, including unequal +/- step weights.

    pair_weights[i] is the product of the two directional activities.
    """
    epsilon, m = length % 2, length // 2
    idle = Fraction(idle)
    coeff = [Fraction(1)] + [Fraction(0)]*m
    for weight in pair_weights:
        weight = Fraction(weight)
        factor = [weight**k / factorial(k)**2 for k in range(m+1)]
        coeff = coefficient_convolution(coeff, factor, m)
    h = [idle**(2*k) / factorial(2*k+epsilon) for k in range(m+1)]
    return factorial(length) * idle**epsilon * sum(coeff[m-k]*h[k]
                                                    for k in range(m+1))


def log_h(epsilon, x):
    """Log H_epsilon(x**2), analytically continued at x=0."""
    if not x:
        return mp.mpf(0)
    return mp.log(mp.cosh(x)) if epsilon == 0 else mp.log(mp.sinh(x)/x)


def _double_factorial_odd(n):
    answer = 1
    for k in range(1, n+1, 2):
        answer *= k
    return answer


def edgeworth_terms(cumulants, order):
    """Universal terms E_0,...,E_order; cumulants[j] uses j-based indexing."""
    variance = cumulants[2]
    answer = [mp.mpf(1)]
    for level in range(1, order+1):
        total = mp.mpf(0)

        def visit(j, remaining, chosen):
            nonlocal total
            if j > 2*level+2:
                if remaining:
                    return
                degree = sum(k*v for k, v in chosen)
                term = mp.mpf((-1)**(degree//2) * _double_factorial_odd(degree-1))
                term /= variance**(degree//2)
                for k, v in chosen:
                    term *= cumulants[k]**v / (factorial(v)*factorial(k)**v)
                total += term
                return
            for v in range(remaining//(j-2)+1):
                visit(j+1, remaining-(j-2)*v, chosen+([(j,v)] if v else []))

        visit(3, 2*level, [])
        answer.append(total)
    return answer


def saddle(length, dimension=None, idle=1, pair_weights=None, order=2):
    """Log count and correction terms. Does not enumerate Bessel zeros.

    Supply either an isotropic dimension or a finite list of pair weights.
    The routine intentionally uses a monotone bracket for the scalar saddle.
    """
    if length < 2:
        raise ValueError("the asymptotic saddle requires length at least 2")
    epsilon, m = length % 2, length // 2
    idle = mp.mpf(idle)
    if idle < 0:
        raise ValueError("idle activity must be nonnegative")
    if epsilon and not idle:
        return {"zero": True, "log_count": mp.ninf}
    if pair_weights is None:
        if dimension is None or dimension < 0 or int(dimension) != dimension:
            raise ValueError("supply an integer dimension or pair_weights")
        factors = [(mp.mpf(1), int(dimension))] if dimension else []
    else:
        weights = [mp.mpf(c) for c in pair_weights]
        if any(c < 0 for c in weights):
            raise ValueError("pair activities must be nonnegative")
        factors = [(c, 1) for c in weights if c]
    if not factors and not idle:
        return {"zero": True, "log_count": mp.ninf}

    def mean(t):
        value = mp.mpf(0)
        for c, multiplicity in factors:
            root = mp.sqrt(c*t)
            value += multiplicity*root*mp.besseli(1, 2*root)/mp.besseli(0, 2*root)
        x = idle*mp.sqrt(t)
        if x:
            value += x*mp.tanh(x)/2 if epsilon == 0 else (x/mp.tanh(x)-1)/2
        return value

    # The first Taylor coefficient supplies a scale-aware initial bracket.
    # The Bernoulli product gives mean(t) <= first_coefficient*t, so this
    # initial high is at or below the true root (up to rounding). Doubling
    # then brackets the root on its own scale, even for extreme activities.
    first_coefficient = (mp.fsum(mult*c for c, mult in factors)
                         + idle**2/(2 if epsilon == 0 else 6))
    low, high = mp.mpf(0), mp.mpf(m)/first_coefficient
    while mean(high) < m:
        low, high = high, 2*high
    for _ in range(mp.mp.prec+12):
        middle = (low+high)/2
        if mean(middle) < m:
            low = middle
        else:
            high = middle
    t = (low+high)/2

    def logarithm(s):
        argument = t*mp.exp(s)
        return (sum(mult*mp.log(mp.besseli(0, 2*mp.sqrt(c*argument)))
                    for c, mult in factors)
                + log_h(epsilon, idle*mp.sqrt(argument)))

    taylor = mp.taylor(logarithm, mp.mpf(0), max(2, 2*order+2))
    cumulants = [taylor[j]*factorial(j) for j in range(len(taylor))]
    variance = cumulants[2]
    terms = edgeworth_terms(cumulants, order)
    log_leading = (mp.loggamma(length+1) + epsilon*mp.log(idle if idle else 1)
                   + taylor[0] - m*mp.log(t) - mp.log(2*mp.pi*variance)/2)
    return {
        "zero": False, "t": t, "mean": cumulants[1], "variance": variance,
        "cumulants": cumulants, "terms": terms, "log_leading": log_leading,
        "log_count": log_leading + mp.log(sum(terms)),
        "relative_envelope": 12/variance,
    }


def numeric_count(length, dimension, idle):
    """Positive finite sum based on exact axis coefficients, for diagnostics."""
    idle = mp.mpf(idle)
    q = axis_coefficients(dimension, length//2)
    return mp.fsum(mp.mpf(comb(length, 2*k)*comb(2*k, k)*q[k])
                   * idle**(length-2*k) for k in range(length//2+1))
