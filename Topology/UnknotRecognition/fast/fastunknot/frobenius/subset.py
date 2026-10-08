"""Square-free multiplication over F2, with ranked subset convolution.

Bit number S of a packed integer is the coefficient of x_S.  This is not
ordinary binary multiplication.  The dense algorithm is the specialization
of Bjoerklund--Husfeldt--Kaski--Koivisto (STOC 2007) to F2.
"""
from __future__ import annotations
from typing import Callable, Iterator

Check = Callable[[], None]
_REVERSED_BYTE = bytes(int(f"{i:08b}"[::-1], 2) for i in range(256))

def noop() -> None:
    pass


def validate(value: int, variables: int) -> None:
    if type(variables) is not int or variables < 0:
        raise ValueError("variables must be a nonnegative integer")
    if type(value) is not int or value < 0:
        raise ValueError("a polynomial must be a nonnegative integer")
    if value.bit_length() > (1 << variables):
        raise ValueError("coefficient outside the declared variable set")


def support(value: int) -> Iterator[int]:
    """Set bit indices, without repeatedly copying a coefficient-sized bigint."""
    if value < 0:
        raise ValueError("negative bitset")
    for byte_index, byte in enumerate(value.to_bytes((value.bit_length()+7)//8, "little")):
        while byte:
            low = byte & -byte
            yield (byte_index << 3) + low.bit_length() - 1
            byte ^= low


def pack(indices, variables: int) -> int:
    if type(variables) is not int or variables < 0:
        raise ValueError("variables must be nonnegative")
    size = 1 << variables
    out = bytearray((size + 7)//8)
    for index in indices:
        if type(index) is not int or not 0 <= index < size:
            raise ValueError("invalid monomial mask")
        out[index >> 3] ^= 1 << (index & 7)
    return int.from_bytes(out, "little")


def _clmul(a: int, b: int, mask: int) -> int:
    """Carryless polynomial product, truncated by a low-bits mask."""
    if a.bit_count() < b.bit_count():
        a, b = b, a
    result = 0
    while b:
        low = b & -b
        result ^= a << (low.bit_length() - 1)
        b ^= low
    return result & mask


def subset_product_ranked(f: int, g: int, variables: int, *, check: Check = noop) -> int:
    """Ranked zeta / convolution / Moebius inverse, exact over F2.

    O(variables^2 * 2^variables) field operations. Rank polynomials at
    each subset are packed into O(variables)-bit integers; large packed
    coefficient vectors are unpacked once and repacked once.
    """
    validate(f, variables); validate(g, variables)
    if not f or not g:
        return 0
    if f == g:
        return f & 1
    if f == 1:
        return g
    if g == 1:
        return f
    n = 1 << variables
    a = [0] * n
    b = [0] * n
    for s in support(f):
        a[s] = 1 << s.bit_count()
    for s in support(g):
        b[s] = 1 << s.bit_count()
    step = 1
    while step < n:
        check()
        for start in range(0, n, 2*step):
            for j in range(start+step, start+2*step):
                a[j] ^= a[j-step]
                b[j] ^= b[j-step]
        step *= 2
    limit = (1 << (variables+1)) - 1
    for s in range(n):
        if not s & 4095:
            check()
        a[s] = _clmul(a[s], b[s], limit)
    del b
    step = 1
    while step < n:
        check()
        for start in range(0, n, 2*step):
            for j in range(start+step, start+2*step):
                a[j] ^= a[j-step]
        step *= 2
    out = bytearray((n+7)//8)
    for s, value in enumerate(a):
        if (value >> s.bit_count()) & 1:
            out[s >> 3] ^= 1 << (s & 7)
    return int.from_bytes(out, "little")


def homogeneous_degree(value: int, *, check: Check = noop) -> int | None:
    """Return its dot degree, -1 for zero, or None for mixed-degree support.

    This checks the actual polynomial; callers never infer homogeneity from
    scanner provenance. Enumerate small bytes rather than shifting bigints.
    """
    if type(value) is not int or value < 0:
        raise ValueError("a polynomial must be a nonnegative integer")
    degree = -1
    for count, mask in enumerate(support(value)):
        if not count & 255:
            check()
        current = mask.bit_count()
        if degree == -1:
            degree = current
        elif degree != current:
            return None
    return degree


def _homogeneous_product(f, g, variables, total_degree, check):
    """Union convolution restricted to the disjoint-union cardinality."""
    if total_degree > variables:
        return 0
    size = 1 << variables
    if total_degree == variables:
        # Only the full monomial can survive. Its coefficient is the binary
        # inner product of f with g indexed by complementary subsets.
        check()
        byte_count = (size + 7) // 8
        reversed_g = int.from_bytes(g.to_bytes(byte_count, "little").translate(_REVERSED_BYTE)[::-1],
                                    "little") >> (8 * byte_count - size)
        return (1 << (size - 1)) if (f & reversed_g).bit_count() & 1 else 0
    a, b = [0] * size, [0] * size
    for s in support(f):
        a[s] = 1
    for s in support(g):
        b[s] = 1
    step = 1
    while step < size:
        check()
        for start in range(0, size, 2 * step):
            for j in range(start + step, start + 2 * step):
                a[j] ^= a[j - step]
                b[j] ^= b[j - step]
        step *= 2
    for s in range(size):
        if not s & 4095:
            check()
        a[s] &= b[s]
    del b
    step = 1
    while step < size:
        check()
        for start in range(0, size, 2 * step):
            for j in range(start + step, start + 2 * step):
                a[j] ^= a[j - step]
        step *= 2
    out = bytearray((size + 7) // 8)
    for s, value in enumerate(a):
        if value and s.bit_count() == total_degree:
            out[s >> 3] ^= 1 << (s & 7)
    return int.from_bytes(out, "little")


def subset_product_fast(f: int, g: int, variables: int, *, check: Check = noop) -> int:
    """Exact dense product, using the cheaper verified homogeneous case.

    Homogeneous inputs use O(variables * 2^variables) binary operations.
    Top-degree products use one packed complementary-subset inner product.
    General inputs retain ranked subset convolution. The final
    cardinality filter is essential: unfiltered union convolution is wrong
    in the square-free ring (it would allow x*x=x).
    """
    validate(f, variables); validate(g, variables)
    if not f or not g:
        return 0
    if f == g:
        return f & 1
    if f == 1:
        return g
    if g == 1:
        return f
    df = homogeneous_degree(f, check=check)
    if df is not None:
        dg = homogeneous_degree(g, check=check)
        if dg is not None:
            return _homogeneous_product(f, g, variables, df + dg, check)
    return subset_product_ranked(f, g, variables, check=check)


def subset_product_sparse(f: int, g: int, variables: int, *,
                          polarize: bool = True, check: Check = noop) -> int:
    """Sparse disjoint-pair product, optionally choosing a polarization.

    FG = F(F+G)+F(0) = G(F+G)+G(0), because H^2=H(0) in this ring.
    """
    validate(f, variables); validate(g, variables)
    if not f or not g:
        return 0
    if f == g:
        return f & 1
    if f == 1:
        return g
    if g == 1:
        return f
    correction = 0
    if polarize:
        d = f ^ g
        choices = [(f.bit_count()*g.bit_count(), f, g, 0),
                   (f.bit_count()*d.bit_count(), f, d, f & 1),
                   (g.bit_count()*d.bit_count(), g, d, g & 1)]
        _, f, g, correction = min(choices, key=lambda item: item[0])
    fs, gs = list(support(f)), list(support(g))
    if len(fs) > len(gs):
        fs, gs = gs, fs
    n = 1 << variables
    out = bytearray((n+7)//8)
    out[0] = correction
    for a in fs:
        check()
        for b in gs:
            if not a & b:
                s = a | b
                out[s >> 3] ^= 1 << (s & 7)
    return int.from_bytes(out, "little")


def subset_product(f: int, g: int, variables: int, *, method: str = "auto",
                   check: Check = noop, dense_limit: int = 18) -> int:
    """Adaptive exact multiplication; dense_limit bounds transform allocation.

    The heuristic changes only performance, never the answer. For the
    asymptotic fast-subset-convolution guarantee use method='fast' explicitly.
    """
    validate(f, variables); validate(g, variables)
    if type(dense_limit) is not int or dense_limit < 0:
        raise ValueError("dense_limit must be a nonnegative integer")
    if method not in {"auto", "sparse", "fast"}:
        raise ValueError("method must be auto, sparse, or fast")
    if method == "fast":
        if variables > dense_limit:
            raise MemoryError("dense transform exceeds configured variable limit")
        return subset_product_fast(f, g, variables, check=check)
    if method == "sparse":
        return subset_product_sparse(f, g, variables, check=check)
    sf, sg, sd = f.bit_count(), g.bit_count(), (f ^ g).bit_count()
    pairs = min(sf*sg, sf*sd, sg*sd)
    if variables <= dense_limit and pairs > 4 * (variables+1) * (1 << variables):
        return subset_product_fast(f, g, variables, check=check)
    return subset_product_sparse(f, g, variables, check=check)
