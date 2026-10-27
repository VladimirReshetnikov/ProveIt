"""Exact packet-Cauchy actions via Toeplitz convolution.

All arithmetic is in (Z / 2**p Z)[U] / (U**2 + U + 1).
An element is an integer pair (a, b), representing a + b*U.  Scalar
inputs use b=0.  This is a kernel prototype, not a SAT solver.

No FFT, division by two in a residue ring, third-party package, or upstream
code is used.  Python's exact integer multiplication implements the packed
convolution; the abstract bit bound is O(M_int(L*(p+log L))).
"""

from __future__ import annotations

from dataclasses import dataclass

Pair = tuple[int, int]


@dataclass(frozen=True)
class Ring:
    p: int

    def __post_init__(self):
        if not isinstance(self.p, int) or isinstance(self.p, bool) or self.p < 1:
            raise ValueError("precision must be a positive integer")

    @property
    def modulus(self) -> int:
        return 1 << self.p

    @property
    def mask(self) -> int:
        return self.modulus - 1

    def normalize(self, x: Pair) -> Pair:
        return x[0] & self.mask, x[1] & self.mask

    def mul(self, x: Pair, y: Pair) -> Pair:
        a, b = x
        c, d = y
        bd = b * d
        return (a * c - bd) & self.mask, (a * d + b * c - bd) & self.mask

    def inverse(self, x: Pair) -> Pair:
        a, b = self.normalize(x)
        norm = (a * a - a * b + b * b) & self.mask
        if norm % 2 == 0:
            raise ValueError("not a unit")
        z = pow(norm, -1, self.modulus)
        return ((a - b) * z) & self.mask, (-b * z) & self.mask

    def batch_inverse(self, xs: list[Pair]) -> list[Pair]:
        if not xs:
            return []
        prefix = [(1, 0)]
        for x in xs:
            prefix.append(self.mul(prefix[-1], x))
        suffix_inverse = self.inverse(prefix[-1])
        answer = [(0, 0)] * len(xs)
        for j in range(len(xs) - 1, -1, -1):
            answer[j] = self.mul(prefix[j], suffix_inverse)
            suffix_inverse = self.mul(suffix_inverse, xs[j])
        return answer


def valuation_integer(x: int) -> int | None:
    if x == 0:
        return None
    x = abs(x)
    return (x & -x).bit_length() - 1


def split_pair(x: Pair) -> tuple[int, Pair] | None:
    vs = [v for v in (valuation_integer(x[0]), valuation_integer(x[1])) if v is not None]
    if not vs:
        return None
    v = min(vs)
    return v, (x[0] >> v, x[1] >> v)


def _validate_packet(L: int, t: int, zeta: Pair):
    if not isinstance(L, int) or isinstance(L, bool) or L < 2 or L & (L - 1):
        raise ValueError("L must be a power of two at least 2")
    if not isinstance(t, int) or not -L <= t < L:
        raise ValueError("t must belong to [-L,L)")
    if (not isinstance(zeta, tuple) or len(zeta) != 2
            or not all(isinstance(x, int) for x in zeta)):
        raise ValueError("zeta must be a pair of exact integers")


def packet_diagonals(L: int, t: int, zeta: Pair, p: int) -> list[Pair]:
    """Return W_d for -L < d < L, at T=t+2*L*zeta.

    W_d = product_{q=-L,...,L-1; q != d}(T-q) / C'(0).
    Every returned coordinate is the canonical residue modulo 2**p.
    Preparation takes O(L) extension-ring operations and two unit inversions.
    """
    _validate_packet(L, t, zeta)
    ring = Ring(p)
    T = t + 2 * L * zeta[0], 2 * L * zeta[1]
    grid = list(range(-L, L))
    denominator_valuation = 0
    denominator_unit = 1
    for q in grid:
        if q == 0:
            continue
        v = valuation_integer(-q)
        if v is None:
            raise ArithmeticError("unexpected zero scalar denominator")
        denominator_valuation += v
        denominator_unit = denominator_unit * ((-q) >> v) & ring.mask
    denominator_inverse = pow(denominator_unit, -1, ring.modulus)

    factors = [split_pair((T[0] - q, T[1])) for q in grid]
    zero_positions = [j for j, f in enumerate(factors) if f is None]
    if len(zero_positions) > 1:
        raise ArithmeticError("more than one zero grid factor")
    product_unit = (1, 0)
    product_valuation = 0
    for f in factors:
        if f is not None:
            v, unit = f
            product_unit = ring.mul(product_unit, ring.normalize(unit))
            product_valuation += v
    product_unit = (product_unit[0] * denominator_inverse & ring.mask,
                    product_unit[1] * denominator_inverse & ring.mask)

    if zero_positions:
        d = grid[zero_positions[0]]
        shift = product_valuation - denominator_valuation
        if shift < 0:
            raise ArithmeticError("nonintegral grid value")
        value = (product_unit[0] << shift & ring.mask,
                 product_unit[1] << shift & ring.mask)
        return [value if q == d else (0, 0) for q in range(-L + 1, L)]

    units = [ring.normalize(f[1]) for f in factors if f is not None]
    inverses = ring.batch_inverse(units)
    answer = []
    for j, d in enumerate(grid):
        if d == -L:
            continue  # This difference is outside an L by L packet.
        f = factors[j]
        if f is None:
            raise ArithmeticError("zero in nonzero branch")
        shift = product_valuation - denominator_valuation - f[0]
        if shift < 0:
            raise ArithmeticError("nonintegral packet entry")
        value = ring.mul(product_unit, inverses[j])
        answer.append((value[0] << shift & ring.mask,
                       value[1] << shift & ring.mask))
    return answer


def convolve_scalar(a: list[int], b: list[int], p: int) -> list[int]:
    """Convolution modulo 2**p by a no-carry integer product.

    With t=min(len(a),len(b)), every unreduced coefficient is less than
    t*2**(2*p).  Byte-aligned radix at least that large prevents carries
    between coefficients.  Byte packing and unpacking are linear in the
    packed bit length, so repeated big-integer shifts are avoided.
    """
    ring = Ring(p)
    if not a or not b:
        return []
    a = [x & ring.mask for x in a]
    b = [x & ring.mask for x in b]
    coefficient_bound = min(len(a), len(b)) * max(a) * max(b)
    if coefficient_bound == 0:
        return [0] * (len(a) + len(b) - 1)
    bits = coefficient_bound.bit_length()
    stride = (bits + 7) // 8
    packed_a = int.from_bytes(b"".join((x & ring.mask).to_bytes(stride, "little") for x in a), "little")
    packed_b = int.from_bytes(b"".join((x & ring.mask).to_bytes(stride, "little") for x in b), "little")
    count = len(a) + len(b) - 1
    data = (packed_a * packed_b).to_bytes(stride * count, "little")
    return [int.from_bytes(data[i * stride:(i + 1) * stride], "little") & ring.mask
            for i in range(count)]


def convolve_pairs(a: list[Pair], b: list[Pair], p: int) -> list[Pair]:
    """Three exact scalar convolutions implement quadratic-ring convolution."""
    ring = Ring(p)
    if not a or not b:
        return []
    ac = convolve_scalar([x[0] for x in a], [x[0] for x in b], p)
    bd = convolve_scalar([x[1] for x in a], [x[1] for x in b], p)
    both = convolve_scalar([x[0] + x[1] for x in a],
                           [x[0] + x[1] for x in b], p)
    return [((x - y) & ring.mask, (z - x - 2 * y) & ring.mask)
            for x, y, z in zip(ac, bd, both)]


def toeplitz_action(diagonals: list[Pair], vector: list[Pair], p: int) -> list[Pair]:
    L = len(vector)
    if L == 0 or len(diagonals) != 2 * L - 1:
        raise ValueError("need 2*L-1 diagonals for a nonempty L-vector")
    c = convolve_pairs(diagonals, list(reversed(vector)), p)
    return [c[2 * L - 2 - x] for x in range(L)]


def dense_action(diagonals: list[Pair], vector: list[Pair], p: int) -> list[Pair]:
    """Literal matched-domain oracle; it does not use convolution."""
    ring = Ring(p)
    L = len(vector)
    if L == 0 or len(diagonals) != 2 * L - 1:
        raise ValueError("need 2*L-1 diagonals for a nonempty L-vector")
    answer = []
    for x in range(L):
        a = b = 0
        for y, v in enumerate(vector):
            c, d = ring.mul(diagonals[y - x + L - 1], v)
            a += c
            b += d
        answer.append((a & ring.mask, b & ring.mask))
    return answer


def boolean_action(diagonals: list[Pair], vector: list[int], p: int,
                   row_mask: list[bool] | None = None) -> list[Pair]:
    """Two narrower integer products for the actual Boolean column input."""
    L = len(vector)
    if (L == 0 or len(diagonals) != 2 * L - 1
            or any(x not in (0, 1) for x in vector)):
        raise ValueError("invalid Boolean Toeplitz input")
    if row_mask is not None and len(row_mask) != L:
        raise ValueError("invalid row mask")
    rev = list(reversed(vector))
    ca = convolve_scalar([x[0] for x in diagonals], rev, p)
    cb = convolve_scalar([x[1] for x in diagonals], rev, p)
    return [(ca[2 * L - 2 - x], cb[2 * L - 2 - x])
            if row_mask is None or row_mask[x] else (0, 0) for x in range(L)]


def dense_boolean_action(diagonals: list[Pair], vector: list[int], p: int,
                         row_mask: list[bool] | None = None) -> list[Pair]:
    """Strong Boolean oracle: skip zero columns and multiply by no bits."""
    L = len(vector)
    if (L == 0 or len(diagonals) != 2 * L - 1
            or any(x not in (0, 1) for x in vector)):
        raise ValueError("invalid Boolean Toeplitz input")
    if row_mask is not None and len(row_mask) != L:
        raise ValueError("invalid row mask")
    ring = Ring(p)
    columns = [y for y, bit in enumerate(vector) if bit]
    answer = []
    for x in range(L):
        if row_mask is not None and not row_mask[x]:
            answer.append((0, 0))
            continue
        a = b = 0
        for y in columns:
            c, d = diagonals[y - x + L - 1]
            a += c
            b += d
        answer.append((a & ring.mask, b & ring.mask))
    return answer


def strided_boolean_action(diagonals: list[Pair], vector: list[int], p: int,
                           row_offset: int, column_offset: int,
                           stride: int) -> list[Pair]:
    """Equal arithmetic-progression row/column sets give a smaller Toeplitz block.

    The full packet has L=stride*len(vector) slots.  The compact vector is
    indexed by columns column_offset+stride*j.  Only rows
    row_offset+stride*j are returned as nonzero positions of an L-vector.
    In particular stride=2 implements each local block at valuation i=0.
    """
    if not isinstance(stride, int) or stride < 1 or not vector:
        raise ValueError("invalid stride or vector")
    if not 0 <= row_offset < stride or not 0 <= column_offset < stride:
        raise ValueError("offset must be less than stride")
    N = len(vector)
    L = stride * N
    if len(diagonals) != 2 * L - 1:
        raise ValueError("full packet dimension differs from stride*length")
    offset = column_offset - row_offset
    compact = [diagonals[offset + stride * d + L - 1]
               for d in range(-N + 1, N)]
    values = boolean_action(compact, vector, p)
    answer = [(0, 0)] * L
    for j, v in enumerate(values):
        answer[row_offset + stride * j] = v
    return answer


def local_action(L: int, t: int, zeta: Pair, p: int, vector: list[Pair],
                 column_mask: list[bool] | None = None,
                 row_mask: list[bool] | None = None) -> list[Pair]:
    """Apply a local masked W block, with zeros on unused packet slots."""
    if len(vector) != L:
        raise ValueError("vector length differs from packet length")
    if column_mask is not None:
        if len(column_mask) != L:
            raise ValueError("invalid column mask")
        vector = [v if keep else (0, 0) for v, keep in zip(vector, column_mask)]
    value = toeplitz_action(packet_diagonals(L, t, zeta, p), vector, p)
    if row_mask is not None:
        if len(row_mask) != L:
            raise ValueError("invalid row mask")
        value = [v if keep else (0, 0) for v, keep in zip(value, row_mask)]
    return value


def direct_polynomial_diagonals(L: int, t: int, zeta: Pair, p: int) -> list[Pair]:
    """Independent oracle: multiply the CANCELLED polynomial before division.

    Uses p+v_2(C'(0)) bits, then cancels the known scalar power of two.
    Does not use factor valuations, denominator batches, or Toeplitz algebra.
    """
    _validate_packet(L, t, zeta)
    denominator = 1
    for q in range(-L, L):
        if q:
            denominator *= -q
    vd = valuation_integer(denominator)
    if vd is None:
        raise ArithmeticError("zero denominator")
    wide = Ring(p + vd)
    ring = Ring(p)
    inv = pow(denominator >> vd, -1, ring.modulus)
    T = t + 2 * L * zeta[0], 2 * L * zeta[1]
    result = []
    for d in range(-L + 1, L):
        product = (1, 0)
        for q in range(-L, L):
            if q != d:
                product = wide.mul(product, (T[0] - q, T[1]))
        if product[0] % (1 << vd) or product[1] % (1 << vd):
            raise ArithmeticError("oracle polynomial is not integral")
        result.append(((product[0] >> vd) * inv & ring.mask,
                       (product[1] >> vd) * inv & ring.mask))
    return result
