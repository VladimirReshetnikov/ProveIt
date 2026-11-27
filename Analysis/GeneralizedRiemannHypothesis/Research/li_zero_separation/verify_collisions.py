#!/usr/bin/env python3
"""Reproduce all Fejer bounds in the note using python-flint 0.9.0."""
from math import comb
from flint import acb, acb_series, arb, arb_series, ctx, fmpz_poly


def li_jet(family, scale, degree, center=0):
    """Right-center coefficients; use faster real arithmetic at real centers."""
    ctx.cap = degree + 1
    u = acb_series([0, 1]) if center else arb_series([0, 1])
    s = (acb(arb(1)/2, center) if center else arb(1)/2) + scale * (1 + u) / (1 - u)
    # Only positive-order coefficients of these local logarithms enter the tests.
    if family == "zeta":
        log_completed = (s.log() + (s - 1).log() - s * arb.pi().log() / 2
                         + (s / 2).lgamma() + s.zeta().log())
    elif family == "beta":
        quarter = arb(1) / 4
        beta = (-s * arb(4).log()).exp() * (s.zeta(quarter) - s.zeta(3 * quarter))
        log_completed = ((s + 1) * (4 / arb.pi()).log() / 2
                         + ((s + 1) / 2).lgamma() + beta.log())
    else:
        raise ValueError(family)
    return [acb(0)] + [acb(k * log_completed[k]) for k in range(1, degree + 1)]


def moment(li, r, n):
    # -D^r li with D = 2 - shift - inverse shift and Hermitian signed indices.
    def signed(index):
        return li[index] if index >= 0 else li[-index].conjugate()

    return -sum((-1)**abs(j) * comb(2 * r, r + j) * signed(n + j)
                for j in range(-r, r + 1))


def statistic(li_a, li_b, n, r, self_test):
    # Shift the Laurent polynomial by r*(n-1) and keep its integer numerator.
    weights = fmpz_poly([n - abs(k) for k in range(1 - n, n)])**r
    degree = r * (n - 1)
    value = arb(0)
    for k in range(degree + 1):
        a = moment(li_a, r, k)
        b = a if self_test else moment(li_b, r, k)
        value += (1 if k == 0 else 2) * int(weights[k + degree]) * (a * b.conjugate()).real
    value /= n**(2 * r)
    if self_test:
        value -= moment(li_a, 2 * r, 0).real
    return value


def verify_bound(second, scale_input, height, n, r, precision, ratio_upper, gap_lower,
                 centers=(0, 0), copies=2):
    ctx.prec = precision
    scale = arb(scale_input)
    self_test = second == "zeta" and centers[0] == centers[1]
    degree = max(n*r, 2*r) if self_test else n*r
    first = li_jet("zeta", scale, degree, centers[0])
    other = first if self_test else li_jet(second, scale, degree, centers[1])
    value = statistic(first, other, n, r, self_test)
    weight = 4 * scale**2 / (scale**2 + arb(height)**2)
    cutoff = weight**2
    ratio = value / cutoff**r
    # copies follows from reversal or conjugation where applicable.
    assert 0 < ratio and ratio < arb(ratio_upper) and ratio < copies
    q = (value / copies)**(arb(1)/r)
    low_endpoint = (cutoff - q) / cutoff**2
    high_endpoint = (16 - q) / 256
    # Prove both endpoint bounds separately to avoid comparing overlapping balls.
    gap_squared = (2*scale)**2 * 12 / (n*n - 1)
    bounds = [(gap_squared * endpoint).sqrt() for endpoint in (low_endpoint, high_endpoint)]
    assert all(b > arb(gap_lower) for b in bounds)
    print(f"zeta/{second}, centers={centers}, T={height}, a={scale_input}, N={n}, r={r}, degree={degree}")
    print("  F / W^(2r) =", ratio.str(22))
    print("  two endpoint bounds =", ", ".join(b.str(16) for b in bounds))
    print(f"  certified separation > {gap_lower}")


def completed_at(family, height):
    s = acb(arb(1)/2, arb(height))
    if family == "zeta":
        return s*(s-1)/2 * arb.pi()**(-s/2) * (s/2).gamma() * s.zeta()
    quarter = arb(1)/4
    beta = 4**(-s) * (s.zeta(quarter) - s.zeta(3*quarter))
    return (4/arb.pi())**((s+1)/2) * ((s+1)/2).gamma() * beta


def main():
    verify_bound("beta", "14.5", 20, 50, 5, 2048, ".682658", ".477")
    verify_bound("beta", "24", 22, 90, 5, 3072, ".737047", ".361")
    verify_bound("zeta", "24", 30, 30, 3, 768, "1.151405", "1.29")
    verify_bound("zeta", ".15", ".15", 3, 1, 256, ".761429", ".082",
                 centers=(21, 14), copies=1)
    ctx.prec = 192
    for family, left, right in (("zeta", "21.022", "21.023"),
                                ("beta", "21.450", "21.451")):
        lo, hi = completed_at(family, left), completed_at(family, right)
        assert lo.imag.contains(0) and hi.imag.contains(0)
        assert lo.real < 0 and hi.real > 0
        print(f"{family} on ({left}, {right}):",
              lo.real.str(12), "to", hi.real.str(12))
    print("All interval inequalities passed.")


if __name__ == "__main__":
    main()
