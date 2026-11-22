"""Exact finite-prefix checks for the resonant Gauss companion (stdlib only)."""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial


@dataclass(frozen=True)
class G:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other):
        return G(self.re + other.re, self.im + other.im)

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return G(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    def scale(self, q):
        return G(self.re * q, self.im * q)

    def norm(self):
        return abs(self.re) + abs(self.im)


ZERO, ONE = G(), G(Q(1))


def add_nat(a, n):
    return a + G(Q(n))


def convolution(x, y, end):
    return [sum((x[j] * y[n - j] for j in range(n + 1)), ZERO)
            for n in range(end + 1)]


def rising(a, k):
    value = ONE
    for j in range(k):
        value *= add_nat(a, j)
    return value


def binomial(c, end):
    b = [ONE]
    for n in range(end):
        b.append((b[n] * add_nat(c, n)).scale(Q(1, n + 1)))
    return b


def verify(a, b, m, end):
    c = add_nat(a + b, m)
    k, r, s = abs(m), max(0, m), min(0, m)
    assert end >= k
    h, inv = [ONE], [ONE]
    for j in range(end):
        prod = h[j] * add_nat(a, r + j) * add_nat(b, r + j)
        h.append(prod.scale(Q(1, (j + 1) * (j + k + 1))))
        n = j + 1
        inv.append(-sum((h[i] * inv[n - i] for i in range(1, n + 1)), ZERO))
    regular = binomial(c, end)
    delta = [ONE] + [ZERO] * end
    assert convolution(inv, h, end) == delta
    assert convolution(regular, binomial(-c, end), end) == delta
    g = convolution(convolution(regular, inv, end), inv, end)
    closed = rising(add_nat(a, s), k) * rising(add_nat(b, s), k)
    assert g[k] == closed.scale(Q((-1) ** k, factorial(k) ** 2))
    radius = 1 / (4 * max(Q(1), (1 + add_nat(a, r).norm()) *
                                  (1 + add_nat(b, r).norm()), 1 + c.norm()))
    assert sum(z.norm() * radius**j for j, z in enumerate(g)) <= 3

    # t^(-s) V has regular coefficients Q[n] and log coefficient g[k] t^k h.
    integ = [ZERO if j == k else z.scale(Q(1, j - k)) for j, z in enumerate(g)]
    reg_coeff = convolution(h, integ, end)
    A, D = add_nat(a, s), add_nat(b, s)
    log_coeff = [ZERO if j < k else g[k] * h[j - k] for j in range(end + 1)]
    # For t^(j-1), recover the entire regular coefficient of L V.
    for j in range(end + 1):
        previous = reg_coeff[j - 1] if j else ZERO
        previous_log = log_coeff[j - 1] if j else ZERO
        recurrence = reg_coeff[j].scale(j*(j-k)) - add_nat(A,j-1)*add_nat(D,j-1)*previous
        log_terms = log_coeff[j].scale(2*j-k) - add_nat(A+D,2*(j-1))*previous_log
        assert recurrence + log_terms == ZERO


def main():
    cases = [(G(Q(1)), G(Q(1))), (G(Q(0)), G(Q(-2))),
             (G(Q(1, 2), Q(-1, 4)), G(Q(-2, 3), Q(1, 3)))]
    total = 0
    for a, b in cases:
        for m in range(-5, 6):
            verify(a, b, m, 13)
            total += 1
    print(f"{total} Gaussian-rational cases: all coefficients through degree 13 verified.")


if __name__ == "__main__":
    main()
