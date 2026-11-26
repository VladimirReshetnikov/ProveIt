"""Evaluate the bounds in the oscillation theorem with mpmath (illustrative)."""
import mpmath as mp

mp.mp.dps = 45
zeta_mass = 2 + mp.euler - mp.log(4 * mp.pi)
print("d    B_chi              lower endpoint       upper endpoint")
for d in (7, 23, 47, 71, 103, 127):
    def legendre(a):
        return 1 if pow(a, (d - 1) // 2, d) == 1 else -1

    values = [(a, legendre(a)) for a in range(1, d)]
    l_zero = -mp.mpf(sum(a * c for a, c in values)) / d
    gamma_sum = mp.fsum(c * mp.loggamma(mp.mpf(a) / d) for a, c in values)
    # Differentiate the Hurwitz-zeta expansion at 0 and use the functional equation.
    logarithmic_derivative = mp.log(2 * mp.pi) + mp.euler - gamma_sum / l_zero
    if d in (7, 23):
        # Independent expansion of Hurwitz zeta at s=1 instead of s=0.
        l_one = -mp.fsum(c * mp.digamma(mp.mpf(a) / d) for a, c in values) / d
        sum_gamma_one = mp.fsum(c * mp.stieltjes(1, mp.mpf(a) / d) for a, c in values)
        check = -mp.log(d) - sum_gamma_one / (d * l_one)
        assert abs(check - logarithmic_derivative) < mp.mpf("1e-38")
    mass = mp.log(d / mp.pi) - mp.euler + 2 * logarithmic_derivative
    print(f"{d:3}", *(mp.nstr(v, 13) for v in (mass, -mass-zeta_mass, -mass+zeta_mass)))
