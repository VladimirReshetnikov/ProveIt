"""Exact fixed-couple menage counts and rational asymptotic coefficients.

Python 3.10+. Standard library only. No import-time tests or file writes.
All indices are ordinary integers (bool is rejected). Series coefficients are
Fractions in ascending powers of x=1/n. No certified numerical inverse is
provided: the report's inverse-envelope constants are existential.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial


def _integer(v, name, minimum=0):
    if type(v) is not int:
        raise TypeError(f"{name} must be an integer, not {type(v).__name__}")
    if v < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    return v


def path_rooks(edges):
    """R_edges, coefficients in ascending powers; edges >= 0."""
    _integer(edges, "edges")
    return tuple(comb(edges + 1 - j, j) for j in range((edges + 1)//2 + 1))


def _product(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            c[i+j] += u*v
    return tuple(c)


def _phi(n, p):
    if len(p) > n+1:
        raise ValueError("rook polynomial degree exceeds board order")
    return sum((-1)**j * c * factorial(n-j) for j, c in enumerate(p))


@lru_cache(None)
def _line(m):
    return _phi(m, path_rooks(2*m-2))


def line_count(m):
    """A127548(m), m>=0; the m=0 value is 1, not a center difference."""
    _integer(m, "m")
    return 1 if m == 0 else _line(m)


@lru_cache(None)
def _circular(n):
    if n == 0:
        return 1
    return sum((-1)**j * (2*n*comb(2*n-j, j)//(2*n-j)) * factorial(n-j)
               for j in range(n+1))


def circular_count(n):
    """Signed Touchard sequence: U0=1, U1=-1, U2=0; counts for n>=3."""
    _integer(n, "n")
    return _circular(n)


@lru_cache(None)
def _fixed(n, s):
    return _phi(n-1, _product(path_rooks(2*s-1), path_rooks(2*n-2*s-3)))


def fixed_count(n, s):
    """A(n,s)=T(n,s+2), n>=3 and 1<=s<=n-2."""
    _integer(n, "n", 3)
    _integer(s, "s", 1)
    if s > n-2:
        raise ValueError("s must be <= n-2")
    return _fixed(n, s)


def triangle_count(n, k):
    """T(n,k), n>=3 and 3<=k<=n."""
    _integer(k, "k", 3)
    return fixed_count(n, k-2)


def adjacent_difference(n, k):
    """T(n,k)-T(n,k-1), 4<=k<=n, including the zero center step."""
    _integer(n, "n", 4)
    _integer(k, "k", 4)
    if k > n:
        raise ValueError("k must be <= n")
    m = n-2*k+4
    return 0 if m == 0 else (1 if m > 0 else -1)*line_count(abs(m))


def _mul(a, b, order):
    c = [Q(0)]*(order+1)
    for i, u in enumerate(a[:order+1]):
        if u:
            for j, v in enumerate(b[:order+1-i]):
                c[i+j] += u*v
    return c


def _inverse(a, order):
    if not a[0]:
        raise ValueError("series constant term must be nonzero")
    c = [Q(0)]*(order+1)
    c[0] = 1/a[0]
    for k in range(1, order+1):
        c[k] = -sum(a[j]*c[k-j] for j in range(1, k+1))/a[0]
    return c


def _fall_recip(start, length, order):
    # 1/(n-start)_length = x^length product_i(1-(start+i)x)^-1.
    out = [Q(0)]*(order+1)
    if length > order:
        return out
    out[length] = Q(1)
    for i in range(length):
        out = _mul(out, [Q((start+i)**j) for j in range(order+1)], order)
    return out


@lru_cache(None)
def _circ_shift(shift, order):
    out = [Q(0)]*(order+1)
    for k in range(order+1):
        term = _fall_recip(shift+1, k, order)
        scale = Q((-1)**k, factorial(k))
        out = [a+scale*b for a, b in zip(out, term)]
    return tuple(out)


@lru_cache(None)
def _line_shift(shift, order):
    out = list(_circ_shift(shift, order))
    for r in range(1, order+1):
        term = _mul(_fall_recip(shift, r, order),
                    _circ_shift(shift+r, order), order)
        out = [a+2*b for a, b in zip(out, term)]
    return tuple(out)


def circular_series(order):
    """Coefficients of U_n/(exp(-2)n!) through x^order."""
    _integer(order, "order")
    return tuple(_circ_shift(0, order))


def line_series(order):
    """Coefficients of L_n/(exp(-2)n!) through x^order."""
    _integer(order, "order")
    return tuple(_line_shift(0, order))


def row_series(order, distance=None):
    """Coefficients of (n-2)A(n,s)/U_n through x^order.

    distance=q=min(s,n-1-s)>=1, or None for the interior coefficient regime.
    The output for None applies uniformly whenever 2*q+1>order. To prevent
    boundary-weight truncation errors, calculations keep an extra degree.
    """
    _integer(order, "order")
    if distance is not None:
        _integer(distance, "distance", 1)
    work = order+1
    inv_u = _inverse(_circ_shift(0, work), work)
    out = [Q(1)]+[Q(0)]*work
    for j in range(1, (order-1)//2+1):
        d = 2*j+2
        rat = _mul(_mul(_fall_recip(0, d, work),
                        _line_shift(d, work), work), inv_u, work)
        for k in range(work+1):
            out[k] += 2*j*rat[k]
        if distance is not None and j >= distance:
            for k in range(work):
                out[k] -= rat[k+1]-2*rat[k]
    return tuple(out[:order+1])


def tv_series(order):
    """Eventual TV expansion against uniform on n-2 legal first images."""
    _integer(order, "order")
    r = row_series(order, 1)
    delta = [Q(1)-r[0]]+[-v for v in r[1:]]
    ans = _mul(delta, [Q(2**k) for k in range(order+1)], order)
    return tuple([Q(0)]+[2*v for v in ans[:order]])


def exact_total_variation(n):
    """Exact rational TV from the uniform law, for any n>=3."""
    _integer(n, "n", 3)
    u = circular_count(n)
    return sum(abs(Q(fixed_count(n,s),u)-Q(1,n-2))
               for s in range(1,n-1))/2


def integer_decimal(value):
    """Serialize a trusted computed integer without changing Python's digit cap."""
    if type(value) is not int:
        raise TypeError("value must be an integer")
    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    value = abs(value)
    chunks = []
    while value:
        value, remainder = divmod(value, 10**9)
        chunks.append(remainder)
    return sign+str(chunks[-1])+"".join(f"{c:09d}" for c in reversed(chunks[:-1]))


def parse_integer_decimal(text):
    """Parse trusted computed decimal output by chunks; no global changes.

    This helper imposes no length limit. Callers must bound untrusted input
    separately; preserving Python's global setting does not enforce its cap.
    """
    if not isinstance(text, str):
        raise TypeError("text must be a string")
    negative = text.startswith("-")
    digits = text[1:] if negative else text
    if not digits or any(c not in "0123456789" for c in digits):
        raise ValueError("text must contain only an optional minus and ASCII digits")
    value = 0
    for start in range(0,len(digits),9):
        part = digits[start:start+9]
        value = value*10**len(part)+int(part)
    return -value if negative else value


def fraction_decimal(value):
    """Exact Fraction serialization using cap-independent integer conversion."""
    value = Q(value)
    numerator = integer_decimal(value.numerator)
    return numerator if value.denominator == 1 else numerator+"/"+integer_decimal(value.denominator)
