"""Exact finite-field helpers for the cyclotomic recurrence regression tests.

Polynomials use coefficients in ascending order. A connection polynomial is
C(z)=1+c_1*z+...+c_R*z**R, so the tested recurrence is
s[n]+c_1*s[n-1]+...+c_R*s[n-R]=0. No floating-point arithmetic is used.
"""
from __future__ import annotations


def determinant_mod(matrix: list[list[int]], prime: int) -> int:
    """Determinant by Gaussian elimination in F_prime (prime is assumed prime)."""
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("A square matrix is required")
    work = [row[:] for row in matrix]
    result = 1
    for col in range(size):
        pivot_row = next((r for r in range(col, size) if work[r][col] % prime), None)
        if pivot_row is None:
            return 0
        if pivot_row != col:
            work[col], work[pivot_row] = work[pivot_row], work[col]
            result = -result
        pivot = work[col][col] % prime
        result = result * pivot % prime
        inverse = pow(pivot, -1, prime)
        for row in range(col + 1, size):
            multiplier = work[row][col] * inverse % prime
            for j in range(col + 1, size):
                work[row][j] = (work[row][j] - multiplier * work[col][j]) % prime
    return result % prime


def schur_sequence_mod(k: int, root: int, prime: int, count: int) -> list[int]:
    """Compute H_k(n;root), 0 <= n < count, by Jacobi--Trudi."""
    if k < 1 or count < 0:
        raise ValueError("Require k >= 1 and count >= 0")
    a, b = k // 2, (k - 1) // 2
    complete = [0] * (count + a + 1)
    complete[0] = 1
    for node in [1] * a + [root] + [root * root % prime] * b:
        for j in range(1, len(complete)):
            complete[j] = (complete[j] + node * complete[j - 1]) % prime
    return [determinant_mod([
        [complete[n - i + j] if n - i + j >= 0 else 0 for j in range(a)]
        for i in range(a)], prime) for n in range(count)]


def berlekamp_massey(sequence: list[int], prime: int) -> list[int]:
    """Minimal connection polynomial for the supplied finite field prefix."""
    current, previous = [1], [1]
    order, displacement, last_discrepancy = 0, 1, 1
    for n in range(len(sequence)):
        discrepancy = (sequence[n] + sum(
            current[i] * sequence[n - i] for i in range(1, order + 1))) % prime
        if discrepancy == 0:
            displacement += 1
            continue
        old_current = current[:]
        multiplier = discrepancy * pow(last_discrepancy, -1, prime) % prime
        required = len(previous) + displacement
        current.extend([0] * max(0, required - len(current)))
        for j, coefficient in enumerate(previous):
            current[j + displacement] = (current[j + displacement]
                                         - multiplier * coefficient) % prime
        if 2 * order <= n:
            order = n + 1 - order
            previous, last_discrepancy, displacement = old_current, discrepancy, 1
        else:
            displacement += 1
    return current[:order + 1]


def phase_multiplicities(polynomial: list[int], root: int, ell: int,
                         prime: int) -> tuple[list[int], list[int]]:
    """Remove all factors 1-root**rho*z; return exponents and remainder."""
    work, exponents = polynomial[:], []
    for rho in range(ell):
        eigenvalue, exponent = pow(root, rho, prime), 0
        while len(work) > 1:
            quotient = [work[0]]
            for j in range(1, len(work) - 1):
                quotient.append((work[j] + eigenvalue * quotient[-1]) % prime)
            if (work[-1] + eigenvalue * quotient[-1]) % prime:
                break
            work = quotient
            exponent += 1
        exponents.append(exponent)
    return exponents, work


def predicted_exponents(k: int, ell: int) -> list[int]:
    """Integer algorithm of Theorem 2.1; no root approximation is required."""
    if k < 1 or ell < 3:
        raise ValueError("Require k >= 1 and ell >= 3")
    M, a = k - 1, k // 2
    result = [0] * ell
    for q in range(k):
        result[q % ell] = max(result[q % ell], 1 + q * (M - q) // 2)
    if ell > M or (ell - M) % 2:
        return result
    q, D = (M - ell) // 2, (M * M - ell * ell) // 8
    cancels = (a + D) % 2 == 1 if k % 2 == 0 else D % 2 == 0
    if cancels:
        result[q % ell] = max(0, D - 2) if ell == 4 and k % 4 == 1 else D
    return result
