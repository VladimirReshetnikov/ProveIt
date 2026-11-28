"""Finite examples for the chapter on clearing a congruence denominator."""
from itertools import product
from math import prod


def check_weak_lift_model():
    # Diagonal entries in the rational representation of the Klein four group.
    identity = (1, 1, 1)
    a = (1, -1, -1)
    b = (-1, 1, -1)
    ab = tuple(u * v for u, v in zip(a, b))
    matrices = [identity, a, b, ab]
    assert all(prod(1 - entry for entry in diag) == 0 for diag in matrices)
    for column in zip(*matrices):
        assert -1 in column
        assert sum(1 - entry for entry in column) == 4


def check_combining_operators():
    # Over F_2, at least one of u, v and u+v vanishes.
    for u, v in product((0, 1), repeat=2):
        assert 0 in (u, v, (u + v) % 2)

    # Exact arithmetic in Z[w] where w^2 = -1-w.
    def multiply(z, q):
        a, b = z
        c, d = q
        return a * c - b * d, a * d + b * c - b * d

    one = (1, 0)
    omega = (0, 1)
    one_plus_omega = (1, 1)
    assert multiply(multiply(omega, omega), omega) == one
    assert multiply(omega, one_plus_omega) == (-1, 0)


def check_fitting_length():
    # For rows (p^a,1), (0,p^b), the relation e2 = -p^a e1
    # leaves exactly p^(a+b) multiples of e1 in the finite quotient.
    p, a, b = 3, 2, 1
    modulus = p ** (a + b)
    order = lambda t: next(k for k in range(1, modulus + 1) if k * t % modulus == 0)
    image_e1, image_e2 = 1, (-p**a) % modulus
    assert (p**a * image_e1 + image_e2) % modulus == 0
    assert (p**b * image_e2) % modulus == 0
    assert order(image_e1) == modulus


if __name__ == "__main__":
    check_weak_lift_model()
    check_combining_operators()
    check_fitting_length()
    print("Verified the fixed-vector, relation-lattice and residue-field examples.")
