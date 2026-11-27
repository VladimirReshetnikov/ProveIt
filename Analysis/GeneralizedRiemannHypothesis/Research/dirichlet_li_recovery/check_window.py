"""Rational certificate for the 255-mode zeta/beta separation theorem.

The first zeros and their order/multiplicity are external analytic inputs.
All inequalities below are checked with exact fractions and no network.
"""

from fractions import Fraction as Q


def log_bounds(x, terms=70):
    """Enclose log(x) by the positive atanh series, for rational x >= 1."""
    y = (x - 1) / (x + 1)
    assert 0 <= y < 1
    lower = 2 * sum(y ** (2 * k + 1) / (2 * k + 1) for k in range(terms))
    error = 2 * y ** (2 * terms + 1) / ((2 * terms + 1) * (1 - y * y))
    return lower, lower + error


def folded_cayley(gamma):
    """Compute (1-1/(1/2+i*gamma))^20 in exact rational coordinates."""
    den = gamma * gamma + Q(1, 4)
    x = (gamma * gamma - Q(1, 4)) / den
    y = gamma / den
    real, imag = Q(1), Q(0)
    for _ in range(20):
        real, imag = real * x - imag * y, imag * x + real * y
    assert real * real + imag * imag == 1
    return real, imag


def spectral_checks():
    # (Label, left/right ordinate, lower/upper real part, minimum |imag|.)
    boxes = [
        ("beta 1", "6.02", "6.03", "-0.987", "-0.984", "0.16"),
        ("beta 2", "10.24", "10.25", "-0.373", "-0.369", "0"),
        ("beta 3", "12.98", "13.00", "0.030", "0.034", "0"),
        ("zeta 1", "14.13", "14.14", "0.155", "0.157", "0.98"),
    ]
    for name, left, right, lower, upper, imag_min in boxes:
        for ordinate in [Q(left), Q(right)]:
            real, imag = folded_cayley(ordinate)
            assert Q(lower) < real < Q(upper)
            assert abs(imag) > Q(imag_min)
        print(f"{name:7s}: folded real part in ({lower},{upper})")
    assert folded_cayley(Q("16.34"))[0] > Q("0.340")

    # On beta's first interval the angle is in (pi,3pi/2).
    # For the others it lies in (0,pi), and the real part increases with gamma.
    z = 1 / (2 * Q("6.03"))
    assert 40 * (z - z**3 / 3) > Q(22, 7)
    assert 40 / (2 * Q("6.02")) < Q(3, 2) * Q(223, 71)
    assert 40 / (2 * Q("10.24")) < Q(223, 71)
    gap = Q(3, 25)
    assert min(Q("0.155") - Q("0.034"), Q("0.340") - Q("0.157"),
               -Q("0.373") + Q("0.984"), 2 * Q("0.16")) > gap
    assert 2 * (1 - Q("0.157")) > Q(5, 3)
    print("Target weights > 5/3; distances from every other atom > 3/25.")


def mass_and_window_checks():
    upper = Q(0)
    for k in range(1, 6):
        n = 2 * k + 1
        lo, hi = log_bounds(Q(n))
        upper += hi / n if k % 2 else -lo / n
    assert upper < Q(3, 10)
    assert Q(157, 50) < Q(223, 71)
    assert log_bounds(Q(157, 50))[0] > Q(114, 100)
    assert Q(223, 71) / 4 > Q(39, 50)
    mass_bound = 2 - 2 * Q(114, 100) + 2 * Q(3, 10) / Q(39, 50)
    assert mass_bound < Q(1, 2)
    folded_mass = 20**2 * Q(1, 2)
    leakage = folded_mass * (2 / (64 * Q(3, 25)))**4
    assert leakage < 1
    assert (Q(5, 3) - 1) / 4 == Q(1, 6)
    assert 4 * (64 - 1) + 3 == 255
    print("Unfolded mass < 1/2; folded mass < 200; Fourier leakage < 1.")
    print("255 indices, stride 20, fourfold 64-point averaging filter.")
    print("Certified separation > ||b||_infinity / 6 for every nonzero real b.")


if __name__ == "__main__":
    spectral_checks()
    mass_and_window_checks()
