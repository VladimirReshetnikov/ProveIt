"""Exact reference computations for the accompanying iPRA report.

These are executable reference algorithms, not extracted object-iPRA proofs.
All searches have the explicit bounds proved in the report.  The enormous
Pell bound is compared in compressed form; it is never materialized.
Only the Python standard library is used.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import gcd, isqrt


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def supported(n, primes):
    """One is smooth; zero and negative integers are not smooth."""
    if n < 1:
        return False
    for p in primes:
        if p < 2:
            raise ValueError("support entries must be at least two")
        for _ in range(n.bit_length()):
            if n % p:
                break
            n //= p
    return n == 1


def prime_factors(n):
    if n < 1:
        raise ValueError("positive argument required")
    result = []
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            result.append(p)
            for _ in range(n.bit_length()):
                if n % p:
                    break
                n //= p
    if n > 1:
        result.append(n)
    return result


def below_power(n, base, exponent):
    """Decide n < base**exponent without constructing that huge power.

    For n>0, floor(log_base(n))+1 divisions by base reduce n to zero.
    The loop is bounded by the input bit length as well as by exponent.
    """
    if n < 0 or base < 2 or exponent < 0:
        raise ValueError("invalid power comparison")
    if n == 0:
        return True
    t = n
    for _ in range(min(exponent, n.bit_length())):
        t //= base
        if t == 0:
            return True
    return False


def pell_bound(D):
    """Return the compressed pair (base, exponent) for B(D)."""
    return 2 * D + 2, 2 * (2 * D + 1) ** 3 + 2


def fundamental_pell(D):
    """Least positive solution, by the bounded search proved in the report.

    For a square D return None.  Worst-case running time is enormous.
    The while condition is the explicit finite bound y < B(D), tested
    without allocating B(D).  A nonsquare input cannot exhaust it by the
    finite Pell construction in the report.
    """
    if D < 1:
        raise ValueError("positive D required")
    if isqrt(D) ** 2 == D:
        return None
    base, exponent = pell_bound(D)
    y = 1
    while below_power(y, base, exponent):
        x = isqrt(D * y * y + 1)
        if x * x - D * y * y == 1:
            return x, y
        y += 1
    raise AssertionError("contradiction to the proved Pell bound")


def pell_power(D, u, v, m):
    x, y = 1, 0
    for _ in range(m):
        x, y = u * x + D * v * y, v * x + u * y
    return x, y


def stormer_neighbors(primes):
    """Return the complete list and an audit table of all Pell candidates."""
    S = tuple(sorted(primes))
    if len(set(S)) != len(S) or not all(prime(p) for p in S):
        raise ValueError("a list of distinct primes is required")
    if 2 not in S:
        return [], []
    answer, table = set(), []
    for es in product(range(3), repeat=len(S)):
        D = 1
        for p, e in zip(S, es):
            D *= p ** e
        sol = fundamental_pell(D)
        if sol is None:
            continue
        x, y = sol
        n = (x - 1) // 2
        keep = bool(x % 2 and supported(n, S) and supported(n + 1, S))
        table.append({"D": D, "x": x, "y": y,
                      "candidate_n": n if x % 2 else None, "retained": keep})
        if keep:
            answer.add(n)
    return sorted(answer), sorted(table, key=lambda row: row["D"])


def poly_eval(coeffs, x):
    value = Q(0)
    for a in reversed(coeffs):
        value = value * x + a
    return value


def no_rational_root_certificate(coeffs):
    if len(coeffs) < 3 or coeffs[0] == 0 or coeffs[-1] == 0:
        return False
    return all(poly_eval(coeffs, Q(p, q)) != 0
               for p in range(-abs(coeffs[0]), abs(coeffs[0]) + 1)
               for q in range(1, abs(coeffs[-1]) + 1))


def root_interval(coeffs, lo, hi, steps):
    lo, hi = Q(lo), Q(hi)
    flo, fhi = poly_eval(coeffs, lo), poly_eval(coeffs, hi)
    if not lo < hi or not flo * fhi < 0:
        raise ValueError("opposite nonzero endpoint signs are required")
    for _ in range(steps):
        mid = (lo + hi) / 2
        fm = poly_eval(coeffs, mid)
        if fm == 0:
            return mid, mid
        if flo * fm < 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return lo, hi


def liouville_K(coeffs, R):
    return max(1, sum(i * abs(c) * (R + 1) ** (i - 1)
                      for i, c in enumerate(coeffs) if i))


def roth_certificate(coeffs, R, p, q, a, b, k, lo=1, hi=2):
    if min(q, a, b, R) < 1 or k < 0:
        return False
    if abs(Q(lo)) > R or abs(Q(hi)) > R or not no_rational_root_certificate(coeffs):
        return False
    r, _ = root_interval(coeffs, lo, hi, 2 * R + k)
    E = abs(Q(p, q) - r) + Q(1, 2 ** k)
    return q ** (2 * b + a) * E ** b < 1


@dataclass(frozen=True)
class Surd:
    """An exact element a+b*sqrt(D), for a fixed nonsquare positive D."""
    a: Q
    b: Q
    D: int = 2

    def __add__(self, other):
        if not isinstance(other, Surd):
            other = Surd(Q(other), Q(0), self.D)
        if self.D != other.D:
            raise ValueError("different quadratic fields")
        return Surd(self.a + other.a, self.b + other.b, self.D)

    def __neg__(self):
        return Surd(-self.a, -self.b, self.D)

    def __sub__(self, other):
        if not isinstance(other, Surd):
            other = Surd(Q(other), Q(0), self.D)
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Surd):
            other = Surd(Q(other), Q(0), self.D)
        if self.D != other.D:
            raise ValueError("different quadratic fields")
        return Surd(self.a * other.a + self.D * self.b * other.b,
                    self.a * other.b + self.b * other.a, self.D)

    def __pow__(self, n):
        if n < 0:
            raise ValueError("natural exponent required")
        ans, base = Surd(Q(1), Q(0), self.D), self
        for _ in range(n.bit_length()):
            if n & 1:
                ans = ans * base
            base = base * base
            n //= 2
        return ans

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        diff = a * a - self.D * b * b
        s = (diff > 0) - (diff < 0)
        return s if a > 0 else -s


def sqrt2_roth_good(p, q, a=1, b=2):
    """Exact inequality |sqrt(2)-p/q| < q^(-2-a/b)."""
    e = Surd(-Q(p, q), Q(1))
    if e.sign() < 0:
        e = -e
    return (e ** b * q ** (2 * b + a) - 1).sign() < 0


def quadratic_example(height_limit, precision=70):
    """Find a good quadratic near cbrt(2) by a finite demonstration search.

    This is NOT an implementation or validation of the full DS bound.
    It returns exact root and target isolating intervals, so the numerical
    inequality is independently checkable using only rational arithmetic.
    """
    xi_lo, xi_hi = root_interval([-2, 0, 0, 1], 1, 2, precision)
    xi_mid = (xi_lo + xi_hi) / 2
    best = None
    for a in range(1, height_limit + 1):
        for b in range(-height_limit, height_limit + 1):
            v = -(a * xi_mid * xi_mid + b * xi_mid)
            cfloor = v.numerator // v.denominator
            for c in (cfloor, cfloor + 1):
                H = max(a, abs(b), abs(c))
                if H > height_limit or gcd(gcd(a, b), c) != 1:
                    continue
                disc = b * b - 4 * a * c
                if disc <= 0 or isqrt(disc) ** 2 == disc:
                    continue
                derivative = abs(2 * a * xi_mid + b)
                if derivative == 0:
                    continue
                residual = abs(poly_eval([c, b, a], xi_mid))
                estimate = residual / derivative
                if best is None or estimate < best[0]:
                    best = estimate, a, b, c, H
    if best is None:
        raise ValueError("no example in this finite search")
    estimate, a, b, c, H = best
    radius = 4 * estimate + Q(1, 2 ** (precision - 4))
    lo, hi = xi_lo - radius, xi_hi + radius
    if poly_eval([c, b, a], lo) * poly_eval([c, b, a], hi) >= 0:
        raise AssertionError("the candidate root was not isolated")
    alpha_lo, alpha_hi = root_interval([c, b, a], lo, hi, precision)
    err = max(abs(xi_lo - alpha_hi), abs(xi_hi - alpha_lo))
    return {"coefficients": [c, b, a], "height": H,
            "xi_interval": [xi_lo, xi_hi],
            "alpha_interval": [alpha_lo, alpha_hi],
            "error_upper": err, "scaled_error_upper": err * H ** 3}
