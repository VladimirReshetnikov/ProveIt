#!/usr/bin/env python3
"""Exact, reproducible quantum-mechanical examples. Run with Python 3.9+.

All matrix entries are rational. The real matrices in these examples are
also complex matrices with zero imaginary part, so transpose is adjoint.
"""

from fractions import Fraction
from math import comb, factorial

Q = Fraction


def matrix(rows):
    return tuple(tuple(Q(value) for value in row) for row in rows)


def make(rows, columns, entry):
    return matrix([[entry(i, j) for j in range(columns)] for i in range(rows)])


def eye(size):
    return make(size, size, lambda i, j: int(i == j))


def transpose(a):
    return tuple(zip(*a))


def scale(c, a):
    return matrix([[c * value for value in row] for row in a])


def add(a, b):
    assert len(a) == len(b) and len(a[0]) == len(b[0])
    return make(len(a), len(a[0]), lambda i, j: a[i][j] + b[i][j])


def subtract(a, b):
    return add(a, scale(-1, b))


def multiply(a, b):
    assert len(a[0]) == len(b)
    return make(len(a), len(b[0]),
                lambda i, j: sum(a[i][h] * b[h][j] for h in range(len(b))))


def kron(a, b):
    rows_b, cols_b = len(b), len(b[0])
    return make(len(a) * rows_b, len(a[0]) * cols_b,
                lambda i, j: a[i // rows_b][j // cols_b] * b[i % rows_b][j % cols_b])


def trace(a):
    assert len(a) == len(a[0])
    return sum(a[i][i] for i in range(len(a)))


def trace_out_first(a, d1, d2):
    """The index of (first, second) is first * d2 + second."""
    assert len(a) == len(a[0]) == d1 * d2
    return make(d2, d2, lambda i, j: sum(a[h * d2 + i][h * d2 + j] for h in range(d1)))


def bell_instrument():
    # rho = (|00> + |11>)(<00| + <11|) / 2. Its entries need no square roots.
    v = matrix([[1], [0], [0], [1]])
    rho = scale(Q(1, 2), multiply(v, transpose(v)))
    identity = eye(2)
    marginal = scale(Q(1, 2), identity)
    assert multiply(rho, rho) == rho and trace(rho) == 1
    assert trace_out_first(rho, 2, 2) == marginal

    x = matrix([[0, 1], [1, 0]])
    plus = scale(Q(1, 2), add(identity, x))
    minus = scale(Q(1, 2), subtract(identity, x))
    assert add(multiply(plus, plus), multiply(minus, minus)) == identity
    probs, branches = [], []
    for outcome in [plus, minus]:
        k = kron(outcome, identity)
        branch = multiply(multiply(k, rho), transpose(k))
        prob = trace(branch)
        reduced = trace_out_first(branch, 2, 2)
        assert prob == Q(1, 2)
        assert scale(1 / prob, reduced) == outcome
        opposite = subtract(identity, outcome)
        assert trace(multiply(opposite, reduced)) == 0
        probs.append(prob)
        branches.append(branch)

    unread = add(*branches)
    assert unread == scale(Q(1, 4), add(eye(4), kron(x, x)))
    assert trace_out_first(unread, 2, 2) == marginal
    print(f"Bell X outcomes have probabilities {probs[0]} and {probs[1]}.")
    print("Bob has the matching X outcome with conditional probability 1 in both branches.")
    print("Discarding Alice's outcome gives Bob the marginal I/2.")


def powers(a, n):
    values = [eye(len(a))]
    for _ in range(n):
        values.append(multiply(values[-1], a))
    return values


def positive_symmetric_2x2(a):
    # Nonnegative principal minors characterize positive semidefinite 2x2 matrices.
    return (a[1][0] == a[0][1] and a[0][0] >= 0 and a[1][1] >= 0
            and a[0][0] * a[1][1] >= a[0][1] ** 2)


def bernstein_measurement(n=15):
    assert n >= 1 and n % 2 == 1
    identity = eye(2)
    x = matrix([[Q(1, 2), Q(1, 4)], [Q(1, 4), Q(1, 2)]])
    p, q = powers(x, n), powers(subtract(identity, x), n)
    effects = [scale(comb(n, j), multiply(p[j], q[n - j])) for j in range(n + 1)]
    total = scale(0, identity)
    first, second, high = total, total, total
    for j, effect in enumerate(effects):
        assert positive_symmetric_2x2(effect)
        total = add(total, effect)
        first = add(first, scale(Q(j, n), effect))
        second = add(second, scale(Q(j, n) ** 2, effect))
        if 2 * j > n:
            high = add(high, effect)
    assert total == identity and first == x
    square_bias = Q(3, 16 * n)
    assert subtract(second, multiply(x, x)) == scale(square_bias, identity)

    # x has eigenvalues 1/4, 3/4; the following is the high-eigenvalue projector.
    projector = scale(Q(1, 2), matrix([[1, 1], [1, 1]]))
    assert multiply(x, projector) == scale(Q(3, 4), projector)
    assert multiply(x, subtract(identity, projector)) == scale(Q(1, 4), subtract(identity, projector))
    error = sum(Q(comb(n, j) * 3 ** (n - j), 4 ** n)
                for j in range((n + 1) // 2, n + 1))
    # For odd n, symmetry makes the two eigenvector errors equal in magnitude.
    assert subtract(projector, high) == matrix([[0, error], [error, 0]])
    assert error <= Q(3, n)  # Chebyshev from variance 3/(16*n) and gap 1/4.
    print(f"The {n + 1} Bernstein effects sum to I and have first moment X.")
    print(f"The second moment exceeds X squared by ({square_bias})I.")
    print(f"The high-outcome effect approximates the spectral projector with exact norm error {error}.")


def oscillator_boundary(size=6):
    # Use unnormalised Fock vectors f_j = (a*)^j f_0, with norm squared j!.
    assert size >= 2
    lowering = make(size, size, lambda i, j: j if i + 1 == j else 0)
    raising = make(size, size, lambda i, j: int(i == j + 1))
    gram = make(size, size, lambda i, j: factorial(j) if i == j else 0)
    assert multiply(transpose(lowering), gram) == multiply(gram, raising)
    number = multiply(raising, lowering)
    assert number == make(size, size, lambda i, j: j if i == j else 0)
    commutator = subtract(multiply(lowering, raising), number)
    top = make(size, size, lambda i, j: int(i == j == size - 1))
    assert commutator == subtract(eye(size), scale(size, top))
    assert trace(commutator) == 0
    print(f"The {size}-state Fock cutoff gives commutator I - {size} P_top.")
    print(f"It acts as I on levels 0 through {size - 2} and as {1-size} on level {size - 1}.")


if __name__ == "__main__":
    bell_instrument()
    bernstein_measurement()
    oscillator_boundary()
