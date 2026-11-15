#!/usr/bin/env python3
"""Exact rational certificates for Euler's and Rodrigues' rotation theorems.

All geometric checks use fractions.Fraction, never floating point arithmetic.
The normalized axis is represented by v/sqrt(q), with v rational and q=v.v>0.
This file is executable supplementary evidence, not a Lean or iPRA proof.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from typing import Iterable, Tuple

Q = Fraction
Vector = Tuple[Q, Q, Q]
Matrix = Tuple[Vector, Vector, Vector]


def vector(values: Iterable) -> Vector:
    result = tuple(Q(x) for x in values)
    if len(result) != 3:
        raise ValueError("a vector must have three entries")
    return result


def matrix(rows: Iterable[Iterable]) -> Matrix:
    result = tuple(vector(row) for row in rows)
    if len(result) != 3:
        raise ValueError("a matrix must have three rows")
    return result


ZERO = vector((0, 0, 0))
IDENTITY = matrix(((1, 0, 0), (0, 1, 0), (0, 0, 1)))


def dot(u: Vector, v: Vector) -> Q:
    return sum((u[i] * v[i] for i in range(3)), Q(0))


def transpose(a: Matrix) -> Matrix:
    return matrix(tuple(tuple(a[j][i] for j in range(3)) for i in range(3)))


def matmul(a: Matrix, b: Matrix) -> Matrix:
    return matrix(tuple(tuple(sum((a[i][k] * b[k][j] for k in range(3)), Q(0))
                              for j in range(3)) for i in range(3)))


def matvec(a: Matrix, v: Vector) -> Vector:
    return vector(dot(row, v) for row in a)


def determinant(a: Matrix) -> Q:
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def cross_matrix(v: Vector) -> Matrix:
    x, y, z = v
    return matrix(((0, -z, y), (z, 0, -x), (-y, x, 0)))


def is_rotation(a: Matrix) -> bool:
    return matmul(transpose(a), a) == IDENTITY and determinant(a) == 1


def quaternion_rotation(a, x, y, z) -> Matrix:
    """Return the proper rational rotation of a nonzero rational quaternion.

    Formula: ((a*a-v.v) I + 2 vv^T + 2a[v]_cross)/(a*a+v.v).
    Positive (a,z) rotates e1 toward e2, fixing e3.
    """
    a = Q(a)
    v = vector((x, y, z))
    v2 = dot(v, v)
    norm2 = a*a + v2
    if norm2 == 0:
        raise ValueError("the zero quaternion does not define a rotation")
    k = cross_matrix(v)
    return matrix(tuple(tuple(((a*a-v2) * IDENTITY[i][j]
                               + 2*v[i]*v[j] + 2*a*k[i][j]) / norm2
                              for j in range(3)) for i in range(3)))


@dataclass(frozen=True)
class AxisCertificate:
    """R = cI+d vv^T/q+(b/q)[v], with q=v.v>0 and c²+b²/q=1.

    Consequently u=v/sqrt(q), s=b/sqrt(q) give the usual unit-axis form.
    """
    v: Vector
    q: Q
    c: Q
    d: Q
    b: Q
    pivot: int
    identity_case: bool


def axis_certificate(rows: Iterable[Iterable]) -> AxisCertificate:
    """Extract a certificate from a rational proper orthogonal matrix.

    The identity test is exact rational equality.  Otherwise choose the
    largest diagonal entry of S=(R+R^T)/2-cI and its column v.
    Every loop has a fixed finite range; rational arithmetic is exact.
    """
    r = matrix(rows)
    if not is_rotation(r):
        raise ValueError("input is not a rational matrix in SO(3)")
    if r == IDENTITY:
        return AxisCertificate(vector((1, 0, 0)), Q(1), Q(1), Q(0), Q(0), 0, True)
    trace = sum((r[i][i] for i in range(3)), Q(0))
    c = (trace - 1) / 2
    d = 1 - c
    symmetric_axis = matrix(tuple(tuple((r[i][j]+r[j][i])/2-c*IDENTITY[i][j]
                                        for j in range(3)) for i in range(3)))
    pivot = max(range(3), key=lambda j: symmetric_axis[j][j])
    v = vector(symmetric_axis[i][pivot] for i in range(3))
    q = dot(v, v)
    w = vector(((r[2][1]-r[1][2])/2,
                (r[0][2]-r[2][0])/2,
                (r[1][0]-r[0][1])/2))
    if not (d > 0 and symmetric_axis[pivot][pivot] >= d/3 and q > 0):
        raise ArithmeticError("the proved positive pivot invariant failed")
    cert = AxisCertificate(v, q, c, d, dot(w, v), pivot, False)
    if not verify_certificate(r, cert):
        raise ArithmeticError("the extracted certificate did not verify")
    return cert


def rodrigues_matrix(cert: AxisCertificate) -> Matrix:
    if cert.q <= 0:
        raise ValueError("q must be positive")
    k = cross_matrix(cert.v)
    return matrix(tuple(tuple(cert.c*IDENTITY[i][j]
                              + cert.d*cert.v[i]*cert.v[j]/cert.q
                              + cert.b*k[i][j]/cert.q
                              for j in range(3)) for i in range(3)))


def verify_certificate(r: Matrix, cert: AxisCertificate) -> bool:
    return (cert.q > 0 and dot(cert.v, cert.v) == cert.q
            and cert.d == 1-cert.c
            and cert.c*cert.c+cert.b*cert.b/cert.q == 1
            and matvec(r, cert.v) == cert.v
            and rodrigues_matrix(cert) == r)


@dataclass(frozen=True)
class AxisApproximation:
    """Coordinate approximations, not an exactly unit rational vector.

    Every coordinate of u and the scalar s have error <=error_bound<2^-n.
    root_lower²<=q<root_upper² proves the error guarantee algebraically.
    """
    u: Vector
    c: Q
    s: Q
    root_lower: Q
    root_upper: Q
    error_bound: Q
    requested_bits: int


def normalized_approximation(cert: AxisCertificate, bits: int) -> AxisApproximation:
    """Construct dyadic-square-root-based normalized axis approximations.

    For q=A/B>0 in lowest terms, sqrt(q)>=1/B.  With
    m=bits+bit_length(2B), floor(sqrt(q) 2^m)/2^m is positive,
    within 2^-m of sqrt(q), and at least 1/(2B).
    Thus division by this rational lower root has coordinate error
    <=2B 2^-m<2^-bits, since |v_i|,|b|<=sqrt(q).
    The fixed shift and integer square root need no unbounded search.
    """
    if not isinstance(bits, int) or bits < 0:
        raise ValueError("bits must be a nonnegative integer")
    q = cert.q
    if q <= 0 or dot(cert.v, cert.v) != q or cert.b*cert.b > q:
        raise ValueError("invalid normalization data")
    m = bits + (2*q.denominator).bit_length()
    scaled = (q.numerator << (2*m)) // q.denominator
    k = isqrt(scaled)
    denominator = 1 << m
    lower = Q(k, denominator)
    upper = Q(k+1, denominator)
    if not (lower > 0 and lower*lower <= q < upper*upper):
        raise ArithmeticError("integer square root interval invariant failed")
    error = (upper-lower)/lower
    if not error < Q(1, 1 << bits):
        raise ArithmeticError("normalization error bound failed")
    return AxisApproximation(vector(x/lower for x in cert.v), cert.c,
                             cert.b/lower, lower, upper, error, bits)


def fraction_text(value: Q) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def certificate_json(cert: AxisCertificate) -> dict:
    return {"v": [fraction_text(x) for x in cert.v],
            "q": fraction_text(cert.q), "c": fraction_text(cert.c),
            "d": fraction_text(cert.d), "b": fraction_text(cert.b),
            "pivot": cert.pivot, "identity_case": cert.identity_case}


def polynomial_rodrigues(u: Vector, c: Q, s: Q) -> Matrix:
    """The polynomial Rodrigues expression, also for unnormalized samples."""
    k = cross_matrix(u)
    return matrix(tuple(tuple(c*IDENTITY[i][j]+(1-c)*u[i]*u[j]+s*k[i][j]
                              for j in range(3)) for i in range(3)))


@dataclass(frozen=True)
class FiniteRotationApproximation:
    """Entirely rational output of the two-branch finite-precision theorem.

    The samples U,C,V need not be exactly normalized.  In the far branch
    they approximate the exact data in cert within 2^(-bits-5).
    In the near branch they are exactly (e1,1,0).
    """
    requested_bits: int
    epsilon: Q
    d_sample: Q
    near_identity: bool
    U: Vector
    C: Q
    V: Q
    coordinate_error_bound: Q
    cert: AxisCertificate


def finite_rotation_approximation(rows: Iterable[Iterable], bits: int) -> FiniteRotationApproximation:
    """Execute the unconditional tolerance branch for an exact rational R.

    A downward dyadic sample has |sample-d|<epsilon²/32.  The rational
    threshold test is identical to the one for arbitrary represented reals.
    This specialization exercises the branching and the finite U,C,V bounds;
    it does not implement arbitrary real-name oracles.
    """
    if not isinstance(bits, int) or bits < 0:
        raise ValueError("bits must be a nonnegative integer")
    r = matrix(rows)
    if not is_rotation(r):
        raise ValueError("input is not a rational matrix in SO(3)")
    epsilon = Q(1, 1 << bits)
    d = (3-sum((r[i][i] for i in range(3)), Q(0)))/2
    scale = 1 << (2*bits+5)
    sample = Q((d.numerator*scale)//d.denominator, scale)
    near = sample <= epsilon*epsilon/8
    if near:
        cert = axis_certificate(IDENTITY)
        return FiniteRotationApproximation(bits, epsilon, sample, True,
                                           cert.v, Q(1), Q(0), Q(0), cert)
    cert = axis_certificate(r)
    appr = normalized_approximation(cert, bits+5)
    return FiniteRotationApproximation(bits, epsilon, sample, False,
                                       appr.u, appr.c, appr.s, appr.error_bound, cert)
