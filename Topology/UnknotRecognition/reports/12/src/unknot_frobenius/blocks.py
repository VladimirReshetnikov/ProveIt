"""Checked matrix arithmetic over F2[x_1,...,x_b]/(x_i^2).

Matrices use conventional row/column order (composition is left multiplication).
The scalar involution shortcut MUST NOT be applied to a matrix unit.
"""
from __future__ import annotations
from dataclasses import dataclass
from .subset import subset_product, validate

Matrix = tuple[tuple[int, ...], ...]


def matrix(rows) -> Matrix:
    out = tuple(tuple(row) for row in rows)
    if not out or not out[0] or any(len(row) != len(out[0]) for row in out):
        raise ValueError("matrix must be nonempty and rectangular")
    if any(type(x) is not int or x < 0 for row in out for x in row):
        raise ValueError("entries must be nonnegative packed polynomials")
    return out


def shape(a: Matrix) -> tuple[int, int]:
    a = matrix(a)
    return len(a), len(a[0])


def identity(n: int) -> Matrix:
    if type(n) is not int or n < 1:
        raise ValueError("positive dimension required")
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def zero(n: int, m: int) -> Matrix:
    if n < 1 or m < 1:
        raise ValueError("positive dimensions required")
    return tuple((0,) * m for _ in range(n))


def add(a: Matrix, b: Matrix) -> Matrix:
    if shape(a) != shape(b):
        raise ValueError("matrix shapes do not agree")
    return tuple(tuple(x ^ y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def mul(a: Matrix, b: Matrix, variables: int, *, method: str = "auto") -> Matrix:
    n, k = shape(a)
    kb, m = shape(b)
    if k != kb:
        raise ValueError("matrix product shape mismatch")
    for row in a+b:
        for value in row:
            validate(value, variables)
    out = [[0]*m for _ in range(n)]
    for i in range(n):
        for t in range(k):
            if a[i][t]:
                for j in range(m):
                    if b[t][j]:
                        out[i][j] ^= subset_product(a[i][t], b[t][j], variables, method=method)
    return matrix(out)


def augmentation(a: Matrix) -> Matrix:
    shape(a)
    return tuple(tuple(x & 1 for x in row) for row in a)


def constant_inverse(a: Matrix) -> Matrix:
    n, m = shape(a)
    if n != m or any(x not in (0, 1) for row in a for x in row):
        raise ValueError("expected a square F2 matrix")
    rows = [sum(v << j for j, v in enumerate(row)) | (1 << (n+i)) for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if (rows[i] >> j) & 1), None)
        if pivot is None:
            raise ValueError("singular augmentation: block is not invertible")
        rows[j], rows[pivot] = rows[pivot], rows[j]
        for i in range(n):
            if i != j and (rows[i] >> j) & 1:
                rows[i] ^= rows[j]
    return tuple(tuple((rows[i] >> (n+j)) & 1 for j in range(n)) for i in range(n))


def unit_inverse(a: Matrix, variables: int, *, verify: bool = True) -> Matrix:
    """Augmentation inverse plus logarithmically many nilpotent squarings."""
    n, m = shape(a)
    if n != m:
        raise ValueError("expected a square matrix")
    for row in a:
        for x in row:
            validate(x, variables)
    a0inv = constant_inverse(augmentation(a))
    one = identity(n)
    power = add(mul(a0inv, a, variables), one)
    series = one
    rounds = 0
    max_rounds = variables.bit_length()  # ceil(log2(variables+1))
    while power != zero(n, n):
        if rounds >= max_rounds:
            raise ArithmeticError("nilpotence bound violated")
        series = add(series, mul(series, power, variables))
        power = mul(power, power, variables)
        rounds += 1
    inverse = mul(series, a0inv, variables)
    if verify and (mul(a, inverse, variables) != one or mul(inverse, a, variables) != one):
        raise ArithmeticError("inverse certificate failed")
    return inverse


def schur(a: Matrix, c: Matrix, d: Matrix, e: Matrix, variables: int) -> Matrix:
    """Remaining differential E + D A^{-1} C after cancelling a unit block."""
    return add(e, mul(mul(d, unit_inverse(a, variables), variables), c, variables))


@dataclass(frozen=True)
class InterfaceData:
    """Sufficient contractions for a low-rank perturbation Schur update.

    For A=A0+UV and B=A0^{-1}, these are
      core=VBU, left=DBU, right=VBC, background=E+DBC.
    This structure validates algebraic shapes, not the provenance of the
    contractions; a topology-aware producer must supply that provenance.
    """
    core: Matrix
    left: Matrix
    right: Matrix
    background: Matrix

    def evaluate(self, variables: int) -> Matrix:
        r, rr = shape(self.core)
        p, rl = shape(self.left)
        rq, q = shape(self.right)
        if r != rr or r != rl or r != rq or shape(self.background) != (p, q):
            raise ValueError("interface shapes do not agree")
        if augmentation(self.core) != zero(r, r):
            raise ValueError("interface core must have radical entries")
        small_inverse = unit_inverse(add(identity(r), self.core), variables)
        return add(self.background, mul(mul(self.left, small_inverse, variables), self.right, variables))


def low_rank_interface(a0_inverse: Matrix, u: Matrix, v: Matrix,
                       c: Matrix, d: Matrix, e: Matrix, variables: int) -> InterfaceData:
    bu = mul(a0_inverse, u, variables)
    bc = mul(a0_inverse, c, variables)
    return InterfaceData(core=mul(v, bu, variables),
                         left=mul(d, bu, variables),
                         right=mul(v, bc, variables),
                         background=add(e, mul(d, bc, variables)))
