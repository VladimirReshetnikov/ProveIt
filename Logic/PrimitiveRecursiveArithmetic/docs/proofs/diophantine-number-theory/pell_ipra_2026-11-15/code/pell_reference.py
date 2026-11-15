#!/usr/bin/env python3
"""Exact, bounded reference algorithms for the constructive Pell article.

Every loop has an explicit finite range. Early returns implement the same
function as a fixed-fuel loop whose state freezes after success. Python's
arbitrary-precision integers and Fraction perform exact arithmetic. These
programs are executable illustrations; tests are not iPRA proof certificates.
"""

from fractions import Fraction


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sqrt_floor(n):
    """Floor square root by a bounded binary-digit scan, with no floats."""
    require(isinstance(n, int) and n >= 0, "square-root input must be natural")
    r = 0
    for k in range((n.bit_length() + 1) // 2 - 1, -1, -1):
        trial = r + (1 << k)
        if trial * trial <= n:
            r = trial
    return r


def valid_discriminant(D):
    return isinstance(D, int) and D >= 2 and sqrt_floor(D) ** 2 != D


def norm(D, z):
    return z[0] * z[0] - D * z[1] * z[1]


def multiply(D, z, w):
    return (z[0] * w[0] + D * z[1] * w[1],
            z[0] * w[1] + z[1] * w[0])


def conjugate(z):
    return (z[0], -z[1])


def power(D, z, exponent):
    require(exponent >= 0, "power exponent must be natural")
    out = (1, 0)
    for _ in range(exponent):
        out = multiply(D, out, z)
    return out


def quadratic_sign(D, A, B):
    """Sign of A+B*sqrt(D), determined entirely by integer comparisons."""
    require(valid_discriminant(D), "D must be nonsquare and at least two")
    sign = lambda t: (t > 0) - (t < 0)
    if A == 0:
        return sign(B)
    if B == 0 or sign(A) == sign(B):
        return sign(A)
    return sign(A) * sign(A * A - D * B * B)


def reduced_state(D, m, d):
    """Integer-only test of 0<=m<=a, 1<=d<=2a, r-m<d<r+m."""
    a = sqrt_floor(D)
    return (0 <= m <= a and 1 <= d <= 2 * a
            and (D - m * m) % d == 0
            and D < (d + m) ** 2
            and (d - m < 0 or (d - m) ** 2 < D))


def cf_certificate(D):
    """Finite continued-fraction certificate and the fundamental solution.

    The period search uses at most S=2a(a+1) steps. The convergent trace has
    2*ell<=2*S entries. The article proves fundamental minimality by the
    finite Legendre lemma; this executable function checks the arithmetic
    invariants and norm identities of its returned trace.
    """
    require(valid_discriminant(D), "D must be nonsquare and at least two")
    a = sqrt_floor(D)
    S = 2 * a * (a + 1)
    first = (a, D - a * a)
    m, d = first
    states = []
    ell = None
    for k in range(1, S + 1):
        require(reduced_state(D, m, d), "invalid reduced CF state")
        c = (a + m) // d
        require(1 <= c <= 2 * a, "CF digit outside proved bound")
        states.append({"index": k, "m": m, "d": d, "digit": c})
        next_m = d * c - m
        require((D - next_m * next_m) % d == 0, "inexact CF division")
        next_d = (D - next_m * next_m) // d
        require(reduced_state(D, next_m, next_d), "CF closure failed")
        m, d = next_m, next_d
        if (m, d) == first:
            ell = k
            break
    require(ell is not None, "period not found in proved finite bound")
    require((states[-1]["m"], states[-1]["d"]) == (a, 1),
            "period endpoint is not (a,1)")
    p2, p1, q2, q1 = 0, 1, 1, 0
    convergents = []
    positive, negative = None, None
    for n in range(2 * ell):
        if n == 0:
            m, d, c = 0, 1, a
        else:
            state = states[(n - 1) % ell]
            m, d, c = state["m"], state["d"], state["digit"]
        require(p1 == m * q1 + d * q2, "first CF identity failed")
        require(D * q1 == m * p1 + d * p2, "second CF identity failed")
        require(p1 * q2 - p2 * q1 == (-1) ** n,
                "CF determinant identity failed")
        p, q = c * p1 + p2, c * q1 + q2
        next_state = states[n % ell]
        k = norm(D, (p, q))
        require(k == (-1) ** (n + 1) * next_state["d"],
                "convergent norm identity failed")
        require(0 < p <= (2 * a + 1) ** (n + 1)
                and 0 < q <= (2 * a + 1) ** (n + 1),
                "convergent coordinate bound failed")
        convergents.append({"index": n, "p": p, "q": q, "norm": k})
        if k == 1 and positive is None:
            positive = (p, q)
        if k == -1 and negative is None:
            negative = (p, q)
        p2, p1, q2, q1 = p1, p, q1, q
    require(positive is not None, "positive unit absent from finite trace")
    endpoint = ell - 1 if ell % 2 == 0 else 2 * ell - 1
    require(positive == (convergents[endpoint]["p"], convergents[endpoint]["q"]),
            "fundamental endpoint formula failed")
    require((negative is None) == (ell % 2 == 0), "negative Pell parity failed")
    if negative is not None:
        require(multiply(D, negative, negative) == positive,
                "negative unit does not square to positive unit")
    return {"D": D, "a": a, "state_bound": S, "period": ell,
            "coordinate_bound": (2 * a + 1) ** (2 * S),
            "states": states, "convergents": convergents,
            "fundamental": positive, "negative": negative}


def fundamental_unit(D):
    return cf_certificate(D)["fundamental"]


def fundamental_by_scan(D, known_positive_unit):
    """Independent bounded selector; the input's y coordinate is the bound."""
    A, B = known_positive_unit
    require(valid_discriminant(D) and A > 1 and B > 0
            and norm(D, known_positive_unit) == 1, "invalid supplied unit")
    for b in range(1, B + 1):
        a = sqrt_floor(D * b * b + 1)
        if a * a == D * b * b + 1:
            return a, b
    raise ArithmeticError("bounded scan missed its supplied witness")


def inverse_step(D, unit, z):
    return multiply(D, conjugate(unit), z)


def reduce_with_threshold(D, unit, z, threshold):
    """Fixed-fuel descent, with a stationary state after reaching threshold.

    The caller must supply a threshold for which the article proves strict
    positive descent. Incorrect supplied units/thresholds are rejected when
    the required invariant fails.
    """
    require(valid_discriminant(D), "invalid discriminant")
    require(unit[0] > 1 and unit[1] > 0 and norm(D, unit) == 1, "invalid unit")
    require(z[0] >= 0 and z[1] >= 0 and threshold >= 0, "invalid descent input")
    original, current, exponent = z, z, 0
    N = norm(D, z)
    for _ in range(z[1]):
        if current[1] <= threshold:
            break
        following = inverse_step(D, unit, current)
        require(following[0] > 0 and 0 <= following[1] < current[1],
                "descent sign/decrease failed; check the unit and threshold")
        require(norm(D, following) == N, "descent norm changed")
        current = following
        exponent += 1
    require(current[1] <= threshold, "fixed descent fuel exhausted")
    require(multiply(D, current, power(D, unit, exponent)) == original,
            "descent reconstruction failed")
    return current, exponent


def classify_norm_one(D, unit, z):
    """Return n for z=unit^n; unit is required to be fundamental."""
    require(norm(D, z) == 1, "input does not have norm one")
    seed, exponent = reduce_with_threshold(D, unit, z, 0)
    require(seed == (1, 0), "norm-one descent did not end at the identity")
    return exponent


def negative_seed_scan(D, unit):
    """Independent bounded negative-Pell decision, scanning 1<=s<=unit.y."""
    require(unit[0] > 1 and unit[1] > 0 and norm(D, unit) == 1, "invalid unit")
    for s in range(1, unit[1] + 1):
        r = sqrt_floor(D * s * s - 1)
        if r * r == D * s * s - 1:
            return r, s
    return None


def classify_negative(D, unit, negative_seed, z):
    """Return n for z=negative_seed*unit^n on nonnegative inputs.

    The supplied unit must be fundamental and negative_seed must be its
    positive norm-minus-one square root, as proved in the article.
    """
    require(norm(D, z) == -1 and norm(D, negative_seed) == -1,
            "negative Pell input required")
    seed, exponent = reduce_with_threshold(D, unit, z, unit[1])
    require(seed == negative_seed, "negative seed mismatch")
    return exponent


def generalized_seeds(D, N, unit):
    """All nonnegative seeds in the article's finite rectangle.

    For nonzero N: 0<=y<=a*abs(N), 0<=x<=(D*a+1)*abs(N).
    Only y is enumerated, since x is forced to be the nonnegative square root.
    Duplicate orbit representatives are intentionally retained.
    """
    require(valid_discriminant(D), "invalid discriminant")
    require(unit[0] > 1 and unit[1] > 0 and norm(D, unit) == 1, "invalid unit")
    if N == 0:
        return [(0, 0)]
    M, a = abs(N), unit[0]
    threshold, xbound = a * M, (D * a + 1) * M
    seeds = []
    for y in range(threshold + 1):
        value = D * y * y + N
        if value < 0:
            continue
        x = sqrt_floor(value)
        if x * x == value:
            require(x <= xbound, "generalized seed bound failed")
            seeds.append((x, y))
    return seeds


def reduce_generalized(D, N, unit, z):
    require(valid_discriminant(D), "invalid discriminant")
    require(unit[0] > 1 and unit[1] > 0 and norm(D, unit) == 1, "invalid unit")
    require(z[0] >= 0 and z[1] >= 0, "nonnegative solution required")
    require(norm(D, z) == N, "wrong generalized norm")
    if N == 0:
        require(z == (0, 0), "nonzero zero-norm input for nonsquare D")
        return (0, 0), 0
    return reduce_with_threshold(D, unit, z, unit[0] * abs(N))


def congruence_period(D, unit, modulus):
    """First return to (1,0) modulo h in at most h*h multiplications."""
    require(modulus >= 1 and norm(D, unit) == 1, "invalid modulus/unit")
    identity = (1 % modulus, 0)
    z = identity
    for t in range(1, modulus * modulus + 1):
        x, y = multiply(D, z, unit)
        z = x % modulus, y % modulus
        if z == identity:
            return t
    raise ArithmeticError("bounded modular return absent")


def sqrt_interval(D, unit, exponent):
    """Exact rational enclosure [D*Y/X, X/Y] of sqrt(D)."""
    require(exponent >= 1 and norm(D, unit) == 1
            and unit[0] > 1 and unit[1] > 0, "positive unit/exponent required")
    x, y = power(D, unit, exponent)
    lower, upper = Fraction(D * y, x), Fraction(x, y)
    require(lower * lower < D < upper * upper, "square-root enclosure failed")
    require(upper - lower == Fraction(1, x * y), "enclosure width identity failed")
    return lower, upper


def sqrt_interval_at_precision(D, unit, precision):
    require(precision >= 0, "precision must be natural")
    lower, upper = sqrt_interval(D, unit, precision + 1)
    require(upper - lower <= Fraction(1, 2 ** precision), "precision bound failed")
    return lower, upper


def dirichlet_certificate(D, Q):
    """Small exact finite-bin construction; intended for modest Q.

    The full huge norm-collision existence algorithm is not run by the test
    suite. This function independently implements and checks its first lemma.
    """
    require(valid_discriminant(D) and Q >= 1, "invalid Dirichlet input")
    bins, floors, scaled_floors = [], [], []
    first_in_bin = [-1] * Q
    collision = None
    for j in range(Q + 1):
        t = sqrt_floor(D * j * j)
        v = sqrt_floor(D * Q * Q * j * j)
        b = v - Q * t
        require(0 <= b < Q, "Dirichlet bin out of range")
        floors.append(t)
        scaled_floors.append(v)
        bins.append(b)
        if first_in_bin[b] >= 0 and collision is None:
            collision = first_in_bin[b], j
        if first_in_bin[b] < 0:
            first_in_bin[b] = j
    require(collision is not None, "finite pigeonhole collision absent")
    i, j = collision
    p, q = floors[j] - floors[i], j - i
    require(1 <= q <= Q and 1 <= p <= D * q, "Dirichlet coordinate bound failed")
    require(quadratic_sign(D, 1 - Q * p, Q * q) > 0
            and quadratic_sign(D, 1 + Q * p, -Q * q) > 0,
            "strict Dirichlet approximation failed")
    return {"D": D, "Q": Q, "p": p, "q": q, "indices": (i, j),
            "bins": bins, "floors": floors, "scaled_floors": scaled_floors,
            "norm": p * p - D * q * q}


def signature(D, p, q):
    k = p * p - D * q * q
    require(k != 0, "zero norm has no signature")
    return (int(k < 0), abs(k) - 1, p % abs(k), q % abs(k))


def signature_code(D, p, q):
    C = 2 * D + 1
    s, m, r, t = signature(D, p, q)
    require(m < C and r < C and t < C, "signature exceeds code range")
    return s * C ** 3 + m * C * C + r * C + t


def quotient_certificate(D, first, second):
    """Integral norm-one quotient from two distinct equal signatures."""
    p, q = first
    r, s = second
    require(q > 0 and s > 0 and q != s, "distinct positive denominators required")
    require(signature(D, p, q) == signature(D, r, s), "signatures differ")
    k = p * p - D * q * q
    A, B = p * r - D * q * s, q * r - p * s
    require(A % abs(k) == 0 and B % abs(k) == 0, "quotient is not integral")
    X, Y = A // k, B // k
    require(Y != 0 and X * X - D * Y * Y == 1, "quotient certificate failed")
    return {"norm": k, "numerator": (A, B), "signed_unit": (X, Y),
            "positive_unit": (abs(X), abs(Y))}


if __name__ == "__main__":
    import json
    rows = []
    for discriminant in (2, 3, 7, 12, 13, 34, 61):
        certificate = cf_certificate(discriminant)
        rows.append({k: certificate[k] for k in
                     ("D", "period", "fundamental", "negative")})
    print(json.dumps(rows, indent=2))
