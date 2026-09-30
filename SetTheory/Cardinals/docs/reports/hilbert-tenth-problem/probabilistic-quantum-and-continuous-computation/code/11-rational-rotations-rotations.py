#!/usr/bin/env python3
"""Exact rational quaternion gates and fixed-length Diophantine certificates.

Python 3.10+, standard library only.  Word generators are nonzero signed
integers.  Rank-r generators 1,...,r represent a^(j-1) b a^(-(j-1)).
This implements the finite compiler, not a concrete universal Higman embedding.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt, lcm
from typing import Callable, Iterable, Sequence

Q = tuple[F, F, F, F]
Matrix = tuple[tuple[F, ...], ...]
Word = tuple[int, ...]


def quat(*v: int | F) -> Q:
    if len(v) != 4:
        raise ValueError("A quaternion must have four coordinates")
    return tuple(F(x) for x in v)  # type: ignore[return-value]


ONE = quat(1, 0, 0, 0)
BASIS = tuple(quat(*(int(i == j) for i in range(4))) for j in range(4))
A = quat(F(3, 5), F(4, 5), 0, 0)
B = quat(F(3, 5), 0, F(4, 5), 0)


def conjugate(q: Q) -> Q:
    return quat(q[0], -q[1], -q[2], -q[3])


def multiply(p: Q, q: Q) -> Q:
    a, b, c, d = p
    e, f, g, h = q
    return quat(a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
                a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def norm_squared(q: Q) -> F:
    return sum((x*x for x in q), F(0))


def denominator(q: Sequence[F]) -> int:
    return lcm(*(x.denominator for x in q))


def reduce_word(w: Iterable[int]) -> Word:
    out: list[int] = []
    for x in w:
        if not isinstance(x, int) or x == 0:
            raise ValueError("Letters must be nonzero signed integers")
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inverse_word(w: Sequence[int]) -> Word:
    return tuple(-x for x in reversed(w))


BINARY = {1: A, -1: conjugate(A), 2: B, -2: conjugate(B)}


def evaluate_binary(w: Iterable[int]) -> Q:
    q = ONE
    for x in w:
        if x not in BINARY:
            raise ValueError("Binary letters are +/-1 and +/-2")
        q = multiply(q, BINARY[x])
    return q


def power_of_five(n: int) -> int | None:
    if n < 1:
        return None
    e = 0
    while n % 5 == 0:
        n //= 5
        e += 1
    return e if n == 1 else None


def decode_binary(q: Q) -> Word | None:
    """Return the unique freely reduced word, or None when q is outside <A,B>."""
    if norm_squared(q) != 1:
        return None
    e = power_of_five(denominator(q))
    if e is None:
        return None
    peeled: list[int] = []
    while e:
        target = 5**(e-1)
        candidates = [(x, multiply(q, BINARY[-x])) for x in (1, -1, 2, -2)]
        candidates = [(x, p) for x, p in candidates if denominator(p) == target]
        if len(candidates) != 1:
            return None
        x, q = candidates[0]
        peeled.append(x)
        e -= 1
    if q != ONE:
        return None
    return tuple(reversed(peeled))


def expand_rank_word(w: Iterable[int], rank: int) -> Word:
    if rank < 1:
        raise ValueError("Rank must be positive")
    out: list[int] = []
    for x in w:
        if not isinstance(x, int) or not 1 <= abs(x) <= rank:
            raise ValueError("Letter outside declared rank")
        j = abs(x)-1
        out.extend([1]*j + [2 if x > 0 else -2] + [-1]*j)
    return reduce_word(out)


def evaluate_rank(w: Iterable[int], rank: int) -> Q:
    return evaluate_binary(expand_rank_word(w, rank))


def decode_rank(q: Q, rank: int) -> Word | None:
    if rank < 1:
        raise ValueError("Rank must be positive")
    w = decode_binary(q)
    if w is None:
        return None
    height = 0
    indexed: list[tuple[int, int]] = []
    for x in w:
        if abs(x) == 1:
            height += x
        else:
            letter = (height, 1 if x > 0 else -1)
            if indexed and indexed[-1] == (letter[0], -letter[1]):
                indexed.pop()
            else:
                indexed.append(letter)
    if height or any(not 0 <= j < rank for j, _ in indexed):
        return None
    return tuple(sign*(j+1) for j, sign in indexed)


def transpose(M: Matrix) -> Matrix:
    return tuple(zip(*M))


def matmul(M: Matrix, N: Matrix) -> Matrix:
    return tuple(tuple(sum((M[i][k]*N[k][j] for k in range(len(N))), F(0))
                       for j in range(len(N[0]))) for i in range(len(M)))


def matvec(M: Matrix, q: Sequence[F]) -> tuple[F, ...]:
    return tuple(sum((a*b for a, b in zip(row, q)), F(0)) for row in M)


def spin(p: Q, q: Q) -> Matrix:
    """Matrix of v -> p v conjugate(q); callers use unit p and q."""
    columns = tuple(multiply(multiply(p, e), conjugate(q)) for e in BASIS)
    return transpose(columns)


IDENTITY = spin(ONE, ONE)
TENSOR_BASIS = tuple(tuple(spin(p, q) for q in BASIS) for p in BASIS)


def frobenius(M: Matrix, N: Matrix) -> F:
    return sum((M[i][j]*N[i][j] for i in range(4) for j in range(4)), F(0))


def rational_sqrt(x: F) -> F | None:
    if x < 0:
        return None
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    return F(a, b) if a*a == x.numerator and b*b == x.denominator else None


def rational_spin_lifts(M: Matrix) -> tuple[tuple[Q, Q], ...]:
    """Recover both rational unit spin lifts, or return an empty tuple.

    Reconstruction and norm checks make this valid even on arbitrary rational
    4x4 matrices, without assuming a rational lift for every rational rotation.
    """
    if len(M) != 4 or any(len(row) != 4 for row in M):
        return ()
    T = tuple(tuple(frobenius(TENSOR_BASIS[i][j], M)/4 for j in range(4))
              for i in range(4))
    col = next((j for j in range(4) if any(T[i][j] for i in range(4))), None)
    if col is None:
        return ()
    c = quat(*(T[i][col] for i in range(4)))
    t = rational_sqrt(norm_squared(c))
    if t is None or t == 0:
        return ()
    p = quat(*(x/t for x in c))
    q = quat(*matvec(transpose(T), p))
    if norm_squared(p) != 1 or norm_squared(q) != 1 or spin(p, q) != M:
        return ()
    return ((p, q), (quat(*(-x for x in p)), quat(*(-x for x in q))))


@dataclass(frozen=True)
class Presentation:
    rank: int
    relators: tuple[Word, ...]

    def __post_init__(self) -> None:
        if self.rank < 1:
            raise ValueError("Rank must be positive")
        for r in self.relators:
            expand_rank_word(r, self.rank)

    def gates(self) -> tuple[Matrix, ...]:
        """Conjugation generators, relator left multiplications, and inverses."""
        forward = [spin(evaluate_rank((j,), self.rank),
                        evaluate_rank((j,), self.rank))
                   for j in range(1, self.rank+1)]
        forward += [spin(evaluate_rank(r, self.rank), ONE) for r in self.relators]
        return tuple(forward + [transpose(M) for M in forward])

    def matrix_membership(self, M: Matrix,
                          word_problem: Callable[[Word], bool]) -> bool:
        """Decide membership using a supplied total word-problem decision oracle."""
        for p, q in rational_spin_lifts(M):
            s, t = decode_rank(p, self.rank), decode_rank(q, self.rank)
            if s is not None and t is not None:
                return bool(word_problem(reduce_word(s + inverse_word(t))))
        return False

    def identity_orbit_membership(self, q: Q,
                                  word_problem: Callable[[Word], bool]) -> bool:
        w = decode_rank(q, self.rank)
        return w is not None and bool(word_problem(w))


def common_gate_denominator(gates: Sequence[Matrix]) -> int:
    if not gates:
        raise ValueError("At least one gate is required")
    return lcm(*(x.denominator for M in gates for row in M for x in row))


def integral_matrices(gates: Sequence[Matrix], D: int) -> tuple[tuple[tuple[int,...],...],...]:
    out = []
    for M in gates:
        rows = []
        for row in M:
            v = tuple(D*x for x in row)
            if any(x.denominator != 1 for x in v):
                raise ValueError("D does not clear the gate denominators")
            rows.append(tuple(int(x) for x in v))
        out.append(tuple(rows))
    return tuple(out)


def certificate_witness(gates: Sequence[Matrix], source: Q,
                        labels: Sequence[int]) -> dict:
    """Construct the unique scaled trace for a zero-based sequence of gate labels."""
    D, d = common_gate_denominator(gates), denominator(source)
    Aint = integral_matrices(gates, D)
    z = [tuple(int(d*x) for x in source)]
    h = [d]
    selectors = []
    for j in labels:
        if not isinstance(j, int) or not 0 <= j < len(gates):
            raise ValueError("Invalid zero-based gate label")
        selectors.append(tuple(int(k == j) for k in range(len(gates))))
        z.append(tuple(sum(Aint[j][r][c]*z[-1][c] for c in range(4)) for r in range(4)))
        h.append(D*h[-1])
    target = quat(*(F(x, h[-1]) for x in z[-1]))
    return {"D": D, "d": d, "u": tuple(int(d*x) for x in source),
            "z": z, "h": h, "selectors": selectors, "target": target}


def certificate_residuals(gates: Sequence[Matrix], source: Q, target: Q,
                         witness: dict) -> list[int]:
    """List the degree<=2 residuals whose squared sum is the quartic certificate.

    This routine checks exact integers and dimensions, but deliberately does not
    enforce valid selector values before evaluating the Boolean residuals.
    """
    D, d, e = common_gate_denominator(gates), denominator(source), denominator(target)
    u, v = tuple(int(d*x) for x in source), tuple(int(e*x) for x in target)
    Aint = integral_matrices(gates, D)
    z, h, selectors = witness["z"], witness["h"], witness["selectors"]
    T, k = len(selectors), len(gates)
    if len(z) != T+1 or len(h) != T+1 or any(len(row) != 4 for row in z) or any(len(row) != k for row in selectors):
        raise ValueError("Malformed certificate shape")
    entries = list(h) + [a for row in z for a in row] + [a for row in selectors for a in row]
    if any(type(a) is not int for a in entries):
        raise ValueError("Witness coordinates must be exact Python integers")
    residuals = [h[0]-d] + [z[0][r]-u[r] for r in range(4)]
    for t in range(T):
        residuals += [s*(s-1) for s in selectors[t]]
        residuals += [sum(selectors[t])-1, h[t+1]-D*h[t]]
        residuals += [z[t+1][r]-sum(selectors[t][j]*Aint[j][r][c]*z[t][c]
                                    for j in range(k) for c in range(4)) for r in range(4)]
    residuals += [e*z[T][r]-h[T]*v[r] for r in range(4)]
    return residuals


def certificate_value(gates: Sequence[Matrix], source: Q, target: Q,
                      witness: dict) -> int:
    return sum(r*r for r in certificate_residuals(gates, source, target, witness))


@dataclass(frozen=True)
class MillerMachine:
    """Miller free-by-free group built from any finite presentation Q.

    Generator order: dummy z, marker q, X, theta_X, theta_R.
    Its word problem does not call the word problem of Q.
    """
    base: Presentation

    @property
    def rank(self) -> int:
        return 2 + 2*self.base.rank + len(self.base.relators)

    @property
    def first_theta(self) -> int:
        return self.base.rank + 3

    def lift_base_word(self, w: Iterable[int]) -> Word:
        return tuple((1 if x > 0 else -1)*(abs(x)+2) for x in w)

    def presentation(self) -> Presentation:
        m, s = self.base.rank, len(self.base.relators)
        xs = tuple(range(3, m+3))
        ts = tuple(range(m+3, m+3+m+s))
        rels: list[Word] = [(1,)]
        rels += [(t, x, -t, -x) for t in ts for x in xs]
        rels += [(ts[j], 2, -ts[j], -x, -2, x) for j, x in enumerate(xs)]
        rels += [(ts[m+j], 2, -ts[m+j]) + inverse_word(self.lift_base_word(r)) + (-2,)
                 for j, r in enumerate(self.base.relators)]
        return Presentation(self.rank, tuple(reduce_word(r) for r in rels))

    def _one_automorphism(self, local_t: int, word: Word) -> Word:
        # Local free base alphabet: q=1, X_j=j+1. Theta indices start at 1.
        m = self.base.rank
        j, sign = abs(local_t)-1, 1 if local_t > 0 else -1
        if j < m:
            x = j+2
            image_q = (-sign*x, 1, sign*x)
        else:
            r = self.base.relators[j-m]
            shifted = tuple((1 if x > 0 else -1)*(abs(x)+1) for x in r)
            image_q = (1,) + (shifted if sign > 0 else inverse_word(shifted))
        out: list[int] = []
        for x in word:
            out.extend(image_q if x == 1 else inverse_word(image_q) if x == -1 else (x,))
        return reduce_word(out)

    def _action(self, theta_word: Word, base_word: Word) -> Word:
        out = base_word
        for t in reversed(theta_word):
            out = self._one_automorphism(t, out)
        return out

    def normal_form(self, w: Iterable[int]) -> tuple[Word, Word]:
        """Quadratic-time free-word normal form for a fixed base presentation.

        The accumulated theta action is q -> u^-1 q v.  The words u and v
        grow only linearly, since all automorphisms fix the X-generators.
        """
        f: list[int] = []
        t: list[int] = []
        u: list[int] = []
        v: list[int] = []

        def push(stack: list[int], seq: Iterable[int]) -> None:
            for a in seq:
                if stack and stack[-1] == -a:
                    stack.pop()
                else:
                    stack.append(a)

        for x in w:
            if not isinstance(x, int) or not 1 <= abs(x) <= self.rank:
                raise ValueError("Miller letter outside declared rank")
            sign, j = (1 if x > 0 else -1), abs(x)
            if j == 1:
                continue
            if j < self.first_theta:
                local = sign*(j-1)
                if local == 1:
                    push(f, inverse_word(u)); push(f, (1,)); push(f, v)
                elif local == -1:
                    push(f, inverse_word(v)); push(f, (-1,)); push(f, u)
                else:
                    push(f, (local,))
            else:
                local_t = sign*(j-self.first_theta+1)
                push(t, (local_t,))
                index = abs(local_t)-1
                if index < self.base.rank:
                    local_x = sign*(index+2)
                    push(u, (local_x,)); push(v, (local_x,))
                else:
                    r = self.base.relators[index-self.base.rank]
                    shifted = tuple((1 if a > 0 else -1)*(abs(a)+1) for a in r)
                    push(v, shifted if sign > 0 else inverse_word(shifted))
        return tuple(f), tuple(t)

    def word_problem(self, w: Word) -> bool:
        return self.normal_form(w) == ((), ())


def commutator(p: Q, q: Q) -> Q:
    """Group commutator p q p^-1 q^-1 for unit quaternions."""
    if norm_squared(p) != 1 or norm_squared(q) != 1:
        raise ValueError("The commutator routine expects unit quaternions")
    return multiply(multiply(multiply(p, q), conjugate(p)), conjugate(q))


def commutator_target_sequence(source: Q, r: Q, s: Q, count: int) -> tuple[Q, ...]:
    if count < 0 or norm_squared(source) != 1 or norm_squared(r) != 1 or norm_squared(s) != 1:
        raise ValueError("Expected unit quaternions and a nonnegative count")
    power = ONE
    values = []
    for _ in range(count):
        conjugate_s = multiply(multiply(power, s), conjugate(power))
        values.append(multiply(source, commutator(s, conjugate_s)))
        power = multiply(power, r)
    return tuple(values)


def order_five_recurrence(r: Q) -> tuple[F, ...]:
    """Low-to-high coefficients for (E-1)(E^2-alpha E+1)(E^2-beta E+1)."""
    if norm_squared(r) != 1:
        raise ValueError("Expected a unit quaternion")
    alpha = 4*r[0]**2-2
    beta = alpha**2-2
    S = alpha+beta+1
    T = alpha*beta+alpha+beta+2
    return tuple(map(F, (-1, S, -T, T, -S, 1)))
