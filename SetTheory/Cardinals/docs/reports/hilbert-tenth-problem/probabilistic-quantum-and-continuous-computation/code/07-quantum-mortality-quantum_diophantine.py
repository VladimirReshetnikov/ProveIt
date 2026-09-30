"""Exact rational Gram packing and natural-number quartic certificates.

Python 3.10+, standard library only. Research reference implementation, not a
high-performance solver. Matrix words are chronological: (i,j) means A_j A_i.
The unbounded Gram search is a total algorithm on positive definite rational
input with s=d+3, by the theorem in the accompanying article; it can be very slow.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import isqrt, lcm
from typing import Iterable, Mapping, Sequence

Matrix = tuple[tuple[F, ...], ...]

def matrix(rows: Sequence[Sequence[int | F]]) -> Matrix:
    a = tuple(tuple(F(x) for x in row) for row in rows)
    if not a or not a[0] or any(len(row) != len(a[0]) for row in a):
        raise ValueError("Expected a nonempty rectangular matrix")
    return a

def zero(m: int, n: int) -> Matrix:
    return tuple((F(0),) * n for _ in range(m))

def eye(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))

def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a))

def mul(a: Matrix, b: Matrix) -> Matrix:
    if len(a[0]) != len(b):
        raise ValueError("Incompatible matrix dimensions")
    bt = transpose(b)
    return tuple(tuple(sum((x*y for x, y in zip(row, col)), F(0))
                       for col in bt) for row in a)

def add(a: Matrix, b: Matrix) -> Matrix:
    if (len(a), len(a[0])) != (len(b), len(b[0])):
        raise ValueError("Incompatible matrix dimensions")
    return tuple(tuple(x+y for x, y in zip(ar, br)) for ar, br in zip(a, b))

def scale(q: int | F, a: Matrix) -> Matrix:
    return tuple(tuple(q*x for x in row) for row in a)

def gram(a: Matrix) -> Matrix:
    return mul(transpose(a), a)

def iszero(a: Matrix) -> bool:
    return not any(x for row in a for x in row)

def word_product(generators: Sequence[Matrix], word: Iterable[int]) -> Matrix:
    p = eye(len(generators[0]))
    for i in word:
        if not 0 <= i < len(generators):
            raise ValueError("Invalid outcome label")
        p = mul(generators[i], p)
    return p

def ldl(q: Matrix) -> tuple[Matrix, tuple[F, ...]]:
    """Return Q=L diag(delta) L^T, checking positive definiteness exactly."""
    d = len(q)
    if len(q[0]) != d or q != transpose(q):
        raise ValueError("Q must be symmetric square")
    l = [[F(i == j) for j in range(d)] for i in range(d)]
    delta: list[F] = []
    for j in range(d):
        v = q[j][j] - sum(l[j][h]**2 * delta[h] for h in range(j))
        if v <= 0:
            raise ValueError("Q is not positive definite")
        delta.append(v)
        for i in range(j+1, d):
            l[i][j] = (q[i][j] - sum(l[i][h]*l[j][h]*delta[h]
                                    for h in range(j))) / v
    return matrix(l), tuple(delta)

def four_squares(n: int) -> tuple[int, int, int, int]:
    """Elementary finite search; O(n) storage/time-scale, not bit-polynomial."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    pairs: dict[int, tuple[int, int]] = {}
    for a in range(isqrt(n)+1):
        for b in range(a, isqrt(n-a*a)+1):
            pairs.setdefault(a*a+b*b, (a, b))
    for s, ab in pairs.items():
        if n-s in pairs:
            return ab + pairs[n-s]
    raise ArithmeticError("Four-square theorem invariant failed")

def elementary_gram(q: Matrix) -> Matrix:
    """An exact 4d by d rational factor B, with B^T B=Q."""
    l, delta = ldl(q)
    lt = transpose(l)
    rows = []
    for j, v in enumerate(delta):
        a, b = v.numerator, v.denominator
        for t in four_squares(a*b):
            rows.append(tuple(F(t, b)*x for x in lt[j]))
    out = matrix(rows)
    assert gram(out) == q
    return out

def gram_search(q: Matrix, s: int | None = None,
                max_height: int | None = None) -> Matrix:
    """Search rational B with s rows by common denominator/numerator height.

    No efficient complexity bound. A cap raises TimeoutError, NOT a proof that
    the factor is nonexistent. Without a cap and s>=d+3, termination follows
    from Meyer and positive definiteness. The search may repeat candidates.
    """
    ldl(q)
    d = len(q)
    s = d+3 if s is None else s
    if s < d:
        raise ValueError("Too few rows for a positive definite Gram matrix")
    h = 1
    while max_height is None or h <= max_height:
        for denominator in range(1, h+1):
            targets = [[q[i][j]*denominator**2 for j in range(d)] for i in range(d)]
            if any(x.denominator != 1 for row in targets for x in row):
                continue
            norms = {int(targets[j][j]) for j in range(d)}
            candidates: dict[int, list[tuple[int, ...]]] = {v: [] for v in norms}
            for v in product(range(-h, h+1), repeat=s):
                norm = sum(x*x for x in v)
                if norm in candidates:
                    candidates[norm].append(v)
            chosen: list[tuple[int, ...]] = []
            def visit(j: int) -> bool:
                if j == d:
                    return True
                for v in candidates[int(targets[j][j])]:
                    if all(sum(x*y for x, y in zip(v, u)) == targets[j][i]
                           for i, u in enumerate(chosen)):
                        chosen.append(v)
                        if visit(j+1):
                            return True
                        chosen.pop()
                return False
            if visit(0):
                out = matrix([[F(chosen[j][i], denominator) for j in range(d)]
                              for i in range(s)])
                assert gram(out) == q
                return out
        h += 1
    raise TimeoutError("Gram search height cap exhausted; existence not refuted")

@dataclass(frozen=True)
class Instrument:
    original: tuple[Matrix, ...]
    c: F
    factor: Matrix
    kraus: tuple[Matrix, ...]  # 0 is the invertible idle outcome
    d: int
    r: int

    @property
    def dimension(self) -> int:
        return self.d + self.r

    def integer_numerators(self) -> tuple[int, tuple[Matrix, ...]]:
        n = lcm(*(x.denominator for a in self.kraus for row in a for x in row))
        return n, tuple(scale(n, a) for a in self.kraus)

    def probability(self, word: Sequence[int]) -> F:
        p = word_product(self.kraus, word)
        return sum((x*x for row in p for x in row), F(0)) / self.dimension


def compile_instrument(matrices: Sequence[Matrix], c: int | F | None = None,
                       factor: Matrix | None = None) -> Instrument:
    ms = tuple(matrix(a) for a in matrices)
    if not ms:
        raise ValueError("At least one generator is required")
    d, k = len(ms[0]), len(ms)
    if any(len(a) != d or len(a[0]) != d for a in ms):
        raise ValueError("Generators must have the same square size")
    s = zero(d, d)
    for a in ms:
        s = add(s, gram(a))
    tr = sum(s[i][i] for i in range(d))
    c = F(isqrt(tr.numerator // tr.denominator)+1) if c is None else F(c)
    if c <= 0:
        raise ValueError("c must be positive")
    q = add(scale(c*c, eye(d)), scale(-1, s))
    ldl(q)  # certifies c^2 I - S is strictly positive definite
    b = elementary_gram(q) if factor is None else matrix(factor)
    if len(b[0]) != d or gram(b) != q:
        raise ValueError("Invalid rational Gram certificate")
    r = (len(b)+k-1)//k
    rows = b + ((F(0),)*d,)*(k*r-len(b))
    dimension = d+r
    a0 = tuple(tuple(F(3, 5) if i == j and i < d else F(i == j)
                     for j in range(dimension)) for i in range(dimension))
    aa = [a0]
    for i, m in enumerate(ms):
        block = m + rows[i*r:(i+1)*r]
        aa.append(scale(F(4, 5)/c, tuple(row+(F(0),)*r for row in block)))
    total = zero(dimension, dimension)
    for a in aa:
        total = add(total, gram(a))
    assert total == eye(dimension)
    return Instrument(ms, c, b, tuple(aa), d, r)

# A small dependency-free sparse polynomial implementation. Monomials are sorted
# tuples of variable names, repeated according to exponent. Coefficients are Z.
@dataclass
class Poly:
    terms: dict[tuple[str, ...], int]

    @staticmethod
    def coerce(x: int | 'Poly') -> 'Poly':
        return x if isinstance(x, Poly) else Poly({(): x} if x else {})

    @staticmethod
    def var(name: str) -> 'Poly':
        return Poly({(name,): 1})

    def __add__(self, other: int | 'Poly') -> 'Poly':
        out = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            out[m] = out.get(m, 0) + c
            if not out[m]:
                del out[m]
        return Poly(out)

    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: int | 'Poly') -> 'Poly':
        return self + -self.coerce(other)

    def __rsub__(self, other: int | 'Poly') -> 'Poly':
        return self.coerce(other) + -self

    def __mul__(self, other: int | 'Poly') -> 'Poly':
        out: dict[tuple[str, ...], int] = {}
        for m, c in self.terms.items():
            for n, e in self.coerce(other).terms.items():
                key = tuple(sorted(m+n))
                out[key] = out.get(key, 0) + c*e
        return Poly({m: c for m, c in out.items() if c})

    __rmul__ = __mul__

    def evaluate(self, values: Mapping[str, int]) -> int:
        total = 0
        for m, c in self.terms.items():
            v = c
            for name in m:
                v *= values[name]
            total += v
        return total

    @property
    def degree(self) -> int:
        return max((len(m) for m in self.terms), default=0)

    def as_json(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items())]

@dataclass
class Certificate:
    dimension: int
    outcomes: int
    length: int
    witnesses: tuple[str, ...]
    inputs: tuple[str, ...]
    residuals: tuple[Poly, ...]

    def value(self, assignment: Mapping[str, int]) -> int:
        names = self.witnesses+self.inputs
        if any(type(assignment[name]) is not int or assignment[name] < 0 for name in names):
            raise ValueError("All certificate coordinates must be natural numbers")
        return sum(r.evaluate(assignment)**2 for r in self.residuals)

    def expanded(self) -> Poly:
        return sum((r*r for r in self.residuals), Poly({}))


def build_certificate(d: int, k: int, n: int) -> Certificate:
    """Uniform quartic: H_j are free signed-pair natural inputs, not constants."""
    if min(d, k, n) < 1:
        raise ValueError("d,k,n must be positive")
    witnesses: list[str] = []
    inputs: list[str] = []
    residuals: list[Poly] = []
    def signed(name: str, is_input: bool = False) -> Poly:
        names = [name+"_p", name+"_m"]
        (inputs if is_input else witnesses).extend(names)
        p, m = (Poly.var(x) for x in names)
        if not is_input:
            residuals.append(p*m)
        return p-m
    h = [[[signed(f"H_{j}_{a}_{b}", True) for b in range(d)]
           for a in range(d)] for j in range(k)]
    x = [[[signed(f"X_{t}_{a}_{b}") for b in range(d)]
           for a in range(d)] for t in range(n+1)]
    y = [[[signed(f"Y_{t}_{a}_{b}") for b in range(d)]
           for a in range(d)] for t in range(n)]
    for t in range(n):
        names = [f"e_{t}_{j}" for j in range(k)]
        witnesses.extend(names)
        es = [Poly.var(name) for name in names]
        residuals.extend(e*(e-1) for e in es)
        residuals.append(sum(es, Poly({}))-1)
        for a in range(d):
            for b in range(d):
                residuals.append(y[t][a][b]-sum((es[j]*h[j][a][b] for j in range(k)), Poly({})))
                residuals.append(x[t+1][a][b]-sum((y[t][a][c]*x[t][c][b] for c in range(d)), Poly({})))
    for a in range(d):
        for b in range(d):
            residuals.append(x[0][a][b]-int(a == b))
            residuals.append(x[n][a][b])
    assert len(witnesses) == n*k+(4*n+2)*d*d
    assert len(residuals) == n*(k+1)+(4*n+3)*d*d
    assert max(r.degree for r in residuals) <= 2
    return Certificate(d, k, n, tuple(witnesses), tuple(inputs), tuple(residuals))


def canonical_assignment(h: Sequence[Matrix], word: Sequence[int]) -> dict[str, int]:
    if not word:
        raise ValueError("The certificate encodes nonempty words")
    d, k = len(h[0]), len(h)
    out: dict[str, int] = {}
    def put(name: str, value: int | F) -> None:
        if F(value).denominator != 1:
            raise ValueError("H must consist of integer matrices")
        v = int(value)
        out[name+"_p"], out[name+"_m"] = max(v, 0), max(-v, 0)
    def put_matrix(prefix: str, a: Matrix) -> None:
        for i in range(d):
            for j in range(d):
                put(f"{prefix}_{i}_{j}", a[i][j])
    for j, a in enumerate(h):
        put_matrix(f"H_{j}", a)
    p = eye(d)
    put_matrix("X_0", p)
    for t, label in enumerate(word):
        if not 0 <= label < k:
            raise ValueError("Invalid word label")
        for j in range(k):
            out[f"e_{t}_{j}"] = int(j == label)
        put_matrix(f"Y_{t}", h[label])
        p = mul(h[label], p)
        put_matrix(f"X_{t+1}", p)
    return out


def signed_example() -> Instrument:
    ms = [matrix([[1,1,0],[0,0,0],[0,0,0]]),
          matrix([[1,0,0],[-1,0,0],[0,0,0]]),
          matrix([[1,-1,0],[0,0,0],[0,0,0]]),
          matrix([[0,0,0],[0,1,0],[0,0,0]]),
          matrix([[0,0,0],[0,1,0],[0,0,0]]),
          matrix([[0,0,0],[0,0,0],[0,0,2]])]
    b = matrix([[1,0,0],[2,0,0],[0,1,0],[0,2,0],[0,0,1],[0,0,2]])
    return compile_instrument(ms, c=3, factor=b)
