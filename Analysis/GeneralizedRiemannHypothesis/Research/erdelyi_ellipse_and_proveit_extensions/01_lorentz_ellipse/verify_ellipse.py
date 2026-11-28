"""Exact Lorentz degrees for explicit Chebyshev counterexamples, using integers only."""
from math import comb


def cayley_coefficients(n):
    # (n^2)^n (1+z)^n P_n((1-z)/(1+z)).
    # Denominators and binomial normalizations are positive, so coefficient signs suffice.
    m = n * n
    prev, curr = [1], [m + 1, -(m + 1)]
    for degree in range(2, n + 1):
        nxt = [0] * (degree + 1)
        for j, a in enumerate(curr):
            nxt[j] += 2 * (m + 1) * a
            nxt[j + 1] -= 2 * (m + 1) * a
        for j, a in enumerate(prev):
            for k, factor in enumerate((1, 2, 1)):
                nxt[j + k] -= m * m * factor * a
        prev, curr = curr, nxt
    return [a + 2 * m**n * comb(n, j) for j, a in enumerate(curr)]


def bernstein_signs(n, D, initial):
    # Coefficient/(D choose j) after elevation, scaled by (D)_n.
    # For fixed i the ratio (D-n choose j-i)/(D choose j)
    # is (j)_i (D-j)_(n-i)/(D)_n.
    for j in range(D // 2 + 1):  # symmetric since n is even
        left, right = [1], [1]
        for i in range(n):
            left.append(left[-1] * (j - i))
            right.append(right[-1] * (D - j - i))
        yield sum(a * left[i] * right[n-i] for i, a in enumerate(initial))


def lorentz_degree(n):
    initial = cayley_coefficients(n)
    assert initial == initial[::-1]
    lo, hi = n - 1, n
    while min(bernstein_signs(n, hi, initial)) < 0:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if min(bernstein_signs(n, mid, initial)) >= 0:
            hi = mid
        else:
            lo = mid
    assert min(bernstein_signs(n, hi, initial)) >= 0
    assert hi == n or min(bernstein_signs(n, hi-1, initial)) < 0
    return hi


if __name__ == "__main__":
    for n in (4, 8, 12, 16, 24, 32, 48, 64):
        d = lorentz_degree(n)
        assert 3 * d * n**2 >= (n**2 + 1)**2
        print(f"{n:3d} {d:6d} {d/n**2:.8f} {4*d/n**3:.8f}")
