"""Precision-aware integral rank-one separation over an unramified 2-adic ring.

The coefficient ring is (Z/2**p)[U]/f(U), for monic f irreducible modulo 2.
This is a local contraction-kernel prototype, not a SAT solver.
Every generated coefficient is a canonical representative at creation precision.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod
from typing import Iterable, Sequence

Element = tuple[int, ...]


def v2(n: int) -> int:
    if n == 0:
        raise ValueError("valuation of zero needs an explicit precision cap")
    return (abs(n) & -abs(n)).bit_length() - 1


def _gf2_mod(a: int, b: int) -> int:
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def _gf2_gcd(a: int, b: int) -> int:
    while b:
        a, b = b, _gf2_mod(a, b)
    return a


def _gf2_square_mod(a: int, f: int) -> int:
    square = sum(((a >> j) & 1) << (2*j) for j in range(a.bit_length()))
    return _gf2_mod(square, f)


def _irreducible_mod_two(f: Sequence[int]) -> bool:
    d = len(f)-1
    bits = sum((c & 1) << j for j, c in enumerate(f))
    x = _gf2_mod(2, bits)
    z = x
    for j in range(1, d+1):
        z = _gf2_square_mod(z, bits)
        if j <= d//2 and _gf2_gcd(z ^ x, bits) != 1:
            return False
    return z == x


@dataclass(frozen=True)
class Ring:
    precision: int
    f: tuple[int, ...] = (0, 1)

    def __post_init__(self) -> None:
        if self.precision < 1 or len(self.f) < 2 or self.f[-1] != 1:
            raise ValueError("positive precision and monic positive-degree f required")
        if not _irreducible_mod_two(self.f):
            raise ValueError("f must be irreducible modulo two")

    @property
    def degree(self) -> int:
        return len(self.f)-1

    @property
    def modulus(self) -> int:
        return 1 << self.precision

    @property
    def zero(self) -> Element:
        return (0,)*self.degree

    @property
    def one(self) -> Element:
        return (1,)+(0,)*(self.degree-1)

    def element(self, value: int | Sequence[int]) -> Element:
        values = (value,)+(0,)*(self.degree-1) if isinstance(value, int) else tuple(value)
        if len(values) != self.degree:
            raise ValueError("wrong coordinate count")
        return tuple(c % self.modulus for c in values)

    def add(self, a: Element, b: Element) -> Element:
        return tuple((x+y) % self.modulus for x, y in zip(a,b))

    def sub(self, a: Element, b: Element) -> Element:
        return tuple((x-y) % self.modulus for x, y in zip(a,b))

    def scale(self, c: int, a: Element) -> Element:
        return tuple((c*x) % self.modulus for x in a)

    def mul(self, a: Element, b: Element) -> Element:
        d = self.degree
        c = [0]*(2*d-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                c[i+j] += x*y
        for k in range(2*d-2,d-1,-1):
            for j in range(d):
                c[k-d+j] -= c[k]*self.f[j]
        return tuple(x % self.modulus for x in c[:d])

    def power(self, a: Element, n: int) -> Element:
        result = self.one
        while n:
            if n & 1:
                result = self.mul(result,a)
            a = self.mul(a,a)
            n >>= 1
        return result

    def valuation(self, a: Element) -> int:
        return min((v2(x) for x in a if x), default=self.precision)

    def inverse(self, a: Element) -> Element:
        if self.valuation(a) != 0:
            raise ValueError("only a unit has an inverse")
        residue = Ring(1,self.f)
        x = residue.power(residue.element(a),(1 << self.degree)-2)
        bits = 1
        while bits < self.precision:
            bits = min(2*bits,self.precision)
            working = Ring(bits,self.f)
            x = working.mul(x,working.sub(working.element(2),working.mul(working.element(a),x)))
        answer = self.element(x)
        if self.mul(a,answer) != self.one:
            raise ArithmeticError("unit inversion failed")
        return answer


@dataclass(frozen=True)
class Mode:
    weight: int
    target: tuple[Element, ...]
    source: tuple[Element, ...]
    pivot: tuple[int,int] | None = None


def separate(matrix: Sequence[Sequence[Element]], ring: Ring) -> list[Mode]:
    """Return an exact modular Smith-weight separation; uses no extra p bits.

    Select a nonzero entry of minimum valuation e. Write it 2**e*u,
    divide its whole row by 2**e at precision p-e, and multiply that row
    by u**(-1). The pivot column times this normalized row is an integral
    rank-one mode. Subtract and repeat on the remaining rows and columns.
    """
    m = len(matrix)
    n = len(matrix[0]) if m else 0
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix is not rectangular")
    remainder = [[ring.element(a) for a in row] for row in matrix]
    active_rows, active_columns = list(range(m)), list(range(n))
    modes: list[Mode] = []
    while active_rows and active_columns:
        e,i,j = min((ring.valuation(remainder[i][j]),i,j)
                    for i in active_rows for j in active_columns)
        if e == ring.precision:
            break
        quotient = Ring(ring.precision-e,ring.f)
        normalized_pivot = quotient.element(tuple(x >> e for x in remainder[i][j]))
        inverse = quotient.inverse(normalized_pivot)
        source = tuple(ring.element(quotient.mul(
            quotient.element(tuple(x >> e for x in remainder[i][k])),inverse))
            for k in range(n))
        target = tuple(remainder[h][j] for h in range(m))
        modes.append(Mode(e,target,source,(i,j)))
        for h in range(m):
            for k in range(n):
                remainder[h][k] = ring.sub(remainder[h][k],ring.mul(target[h],source[k]))
        if any(remainder[i][k] != ring.zero for k in range(n)) or any(
                remainder[h][j] != ring.zero for h in range(m)):
            raise ArithmeticError("pivot row or column did not vanish")
        active_rows.remove(i)
        active_columns.remove(j)
    if any(a != ring.zero for row in remainder for a in row):
        raise ArithmeticError("nonzero final remainder")
    if any(modes[j].weight > modes[j+1].weight for j in range(len(modes)-1)):
        raise ArithmeticError("Smith weights are not monotone")
    return modes


def reconstruct(modes: Iterable[Mode], rows: int, columns: int, ring: Ring) -> list[list[Element]]:
    result = [[ring.zero for _ in range(columns)] for _ in range(rows)]
    for mode in modes:
        for i in range(rows):
            for j in range(columns):
                result[i][j] = ring.add(result[i][j],ring.mul(mode.target[i],mode.source[j]))
    return result


def kernel_data(a: int, t: int, zeta: Sequence[int], ring: Ring) -> tuple[Element, Element]:
    """Return T and Gamma(T)/T at p+i bits, sufficient for crossing ratios.

    Gamma=C/C'(0), C=prod_{v=-L}^{L-1}(T-v). All exact nonunit
    division is done on extra-precision polynomial evaluation; this is the
    existing kernel preparation, separate from the no-extra-bits separator.
    """
    L = 1 << a
    i = v2(t)
    if not (-L <= t < L) or i >= a:
        raise ValueError("t must be a retained nonzero node")
    cprime = prod(-v for v in range(-L,L) if v)
    loss = v2(cprime)
    high = Ring(ring.precision+i+loss,ring.f)
    T = high.add(high.element(t),high.scale(2*L,high.element(zeta)))
    numerator = high.one
    # Cancel the factor T before division, obtaining Gamma(T)/T.
    for v in range(-L,L):
        if v:
            numerator = high.mul(numerator,high.sub(T,high.element(v)))
    if any(x % (1 << loss) for x in numerator):
        raise ArithmeticError("kernel polynomial lacks certified divisibility")
    medium = Ring(ring.precision+i,ring.f)
    normalized = medium.element(tuple(x >> loss for x in numerator))
    c = medium.scale(pow(cprime >> loss,-1,medium.modulus),normalized)
    return medium.element(T),c


def _ratio(num: Element, den: Element, working: Ring, output: Ring) -> Element:
    e = working.valuation(den)
    if e == working.precision or e > working.precision-output.precision:
        raise ValueError("insufficient ratio precision")
    if any(x % (1 << e) for x in num):
        raise ArithmeticError("ratio is not integral")
    numerator = output.element(tuple(x >> e for x in num))
    denominator = output.element(tuple(x >> e for x in den))
    return output.mul(numerator,output.inverse(denominator))


def crossing_kernel(a: int, t: int, zeta: Sequence[int], rows: Sequence[int],
                    columns: Sequence[int], ring: Ring) -> list[list[Element]]:
    """Actual W crossing block; slots have a common bit at valuation i."""
    i = v2(t)
    working = Ring(ring.precision+i,ring.f)
    T,c = kernel_data(a,t,zeta,ring)
    return [[ring.mul(ring.element(c),_ratio(
        T,working.add(T,working.element(x-y)),working,ring)) for y in columns] for x in rows]


def padded_restricted_modes(a: int, t: int, zeta: Sequence[int],
                            rows: Sequence[int], columns: Sequence[int], ring: Ring) -> list[Mode]:
    """Strong comparator: full-block Cauchy basis, restricted to real slots.

    Zero terms are removed, and every common source valuation is transferred
    into its target. Thus the comparator is stronger than simply retaining
    the published padded weights.
    """
    i = v2(t)
    L, R = 1 << a, 1 << i
    if not rows or not columns:
        return []
    orientation = (rows[0] >> i) & 1
    if any(((x >> i) & 1) != orientation for x in (*rows,*columns)):
        raise ValueError("all slots must belong to one crossing orientation")
    slots = [orientation*R+(j % R)+2*R*(j//R) for j in range(L//2)]
    if any(x not in slots for x in (*rows,*columns)):
        raise ValueError("slot is outside the orientation")
    working = Ring(ring.precision+i,ring.f)
    T,c_high = kernel_data(a,t,zeta,ring)
    c = ring.element(c_high)
    P = [ring.one for _ in rows]
    Q = [ring.one for _ in columns]
    result: list[Mode] = []
    for b,s in enumerate(slots):
        f = [ring.mul(P[k],_ratio(T,working.add(T,working.element(x-s)),working,ring))
             for k,x in enumerate(rows)]
        g = [ring.mul(Q[k],_ratio(T,working.add(T,working.element(s-y)),working,ring))
             for k,y in enumerate(columns)]
        source_loss = min((ring.valuation(x) for x in g),default=ring.precision)
        target = [ring.mul(c,x) for x in f]
        target_loss = min((ring.valuation(x) for x in target),default=ring.precision)
        if source_loss+target_loss < ring.precision:
            source = tuple(ring.element(tuple(v >> source_loss for v in x)) for x in g)
            target = tuple(ring.scale(1 << source_loss,x) for x in target)
            result.append(Mode(source_loss+target_loss,target,source))
        P = [ring.mul(P[k],_ratio(working.element(x-s),
             working.add(T,working.element(x-s)),working,ring)) for k,x in enumerate(rows)]
        Q = [ring.mul(Q[k],_ratio(working.element(s-y),
             working.add(T,working.element(s-y)),working,ring)) for k,y in enumerate(columns)]
    return result


def tuple_count(weights: Sequence[int], precision: int) -> int:
    """Exact abstract nonnegative mode-tuple inventory, total weight < p."""
    if any(w <= 0 for w in weights):
        raise ValueError("positive weights required")
    dp = [1]+[0]*(precision-1)
    for w in weights:
        for n in range(w,precision):
            dp[n] += dp[n-w]
    return sum(dp)
