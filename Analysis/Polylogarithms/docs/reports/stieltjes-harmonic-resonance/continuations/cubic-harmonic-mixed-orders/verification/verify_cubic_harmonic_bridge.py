#!/usr/bin/env python3
"""Verify the cubic--harmonic identity using independent analytic routes.

The principal result uses python-flint / Arb ball arithmetic and the
explicit Binet tail bound proved in Section 2 of the accompanying article.  Independent
mpmath quadratures are numerical diagnostics, not interval certificates.
"""
import json
from pathlib import Path

import flint
from flint import arb, arb_series, ctx
import mpmath as mp


def zeta_prime_arb(s, a=1):
    return arb_series([s, 1], 2).zeta(a)[1]


def certified_cubic(ncut=50, terms=24, dps=100):
    ctx.dps = dps
    gamma = arb.const_euler()
    laurent = arb_series([1, 1], 4).zeta(deflate=True)
    gamma1 = -laurent[1]
    gamma2 = 2 * laurent[2]
    zeta2 = arb(2).zeta()
    harmonic = arb(0)
    series = arb(0)
    for n in range(1, ncut):
        logn = arb(n).log()
        series += (harmonic - gamma - logn) * logn / n
        harmonic += arb(1) / n
    series += zeta_prime_arb(2, ncut) / 2
    for k in range(1, terms + 1):
        series += arb.bernoulli(2*k) * zeta_prime_arb(2*k+1, ncut) / (2*k)
    error = abs(arb.bernoulli(2*terms+2)) / (2*terms+2)
    error *= -zeta_prime_arb(2*terms+3, ncut)
    series += arb(0, error)
    cubic = 3*zeta2 + 6*gamma2 + 6*series
    eta = (3*zeta2 - cubic - 6*gamma*gamma1) / 6
    z0 = arb_series([0, 1], 4).zeta()
    zeta00 = 2*z0[2]
    zeta000 = 6*z0[3]
    log2pi = (2*arb.pi()).log()
    omega3 = (
        6*eta - 8*zeta000 - 12*(gamma+log2pi)*zeta00
        - log2pi**3 - 6*gamma*log2pi**2 + 5*gamma**3
        + 12*gamma*gamma1 - arb(3)*gamma*zeta2/2
        - arb(3)*zeta2/2 + arb(3)*zeta_prime_arb(2)/2
    )
    return {
        "method": "Arb ball arithmetic plus explicit Binet tail bound",
        "precision_decimal_digits": dps,
        "cutoff_N": ncut,
        "Bernoulli_terms_K": terms,
        "analytic_error_bound_for_Q": (6*error).str(35),
        "cubic_finite_part_arb": cubic.str(90),
        "eta_arb": eta.str(90),
        "omega_third_derivative_arb": omega3.str(90),
        "cubic_ball": cubic,
        "eta_ball": eta,
    }


def convolve(a, b, degree):
    return [mp.fsum(a[j]*b[k-j] for j in range(k+1))
            for k in range(degree+1)]


def independent_cubic(dps=70):
    mp.mp.dps = dps
    degree = 130
    h = [-mp.euler] + [(-1)**(k+1)*mp.zeta(k+1)
                      for k in range(1, degree+3)]
    h2 = convolve(h, h, degree+1)
    h3 = [mp.fsum(h[j]*h2[k-j] for j in range(k+1))
          for k in range(degree+1)]
    c = [h3[k]-3*h2[k+1]+3*h[k+2] for k in range(degree+1)]
    split = mp.mpf(1)/4
    lower = mp.fsum(c[k]*split**(k+1)/(k+1)
                   for k in range(degree+1))
    def remainder(x):
        return (mp.digamma(x)**3 + x**(-3) + 3*mp.euler/x**2
                - 3*(mp.zeta(2)-mp.euler**2)/x)
    return mp.mpf(1)/2 + 3*mp.euler + lower + mp.quad(remainder, [split, 1])


def independent_eta(dps=70):
    """Use the already established, independently regularized Mellin kernel."""
    mp.mp.dps = dps
    def kernel_regular(t):
        if t < mp.mpf('0.05'):
            # A=t/(exp(t)-1)-1; B=log((1-exp(-t))/t).
            a = -t/2 + mp.fsum(mp.bernoulli(2*k)*t**(2*k)/mp.factorial(2*k)
                              for k in range(1, 24))
            b = -t/2 + mp.fsum(mp.bernoulli(2*k)*t**(2*k)
                              / ((2*k)*mp.factorial(2*k))
                              for k in range(1, 24))
        else:
            a = t/mp.expm1(t)-1
            b = mp.log(-mp.expm1(-t)/t)
        return -(mp.log(t)*a+(1+a)*b)/t
    first = mp.quad(lambda t: mp.log(t)*kernel_regular(t),
                    [0, mp.mpf('0.05'), mp.mpf('0.25'), 1])
    second = mp.quad(lambda t: -mp.log(t)*mp.log(-mp.expm1(-t))/mp.expm1(t),
                     [1, 3, 10, mp.inf])
    return (mp.euler**3/6-mp.euler*mp.zeta(2)/2+mp.zeta(3)/3+first+second)


def main():
    report = certified_cubic()
    cubic_ball = report.pop("cubic_ball")
    eta_ball = report.pop("eta_ball")
    cubic = independent_cubic()
    eta = independent_eta()
    predicted = 3*mp.zeta(2)-6*eta-6*mp.euler*mp.stieltjes(1)
    report.update({
        "flint_version": flint.__version__,
        "mpmath_version": mp.__version__,
        "independent_regularized_digamma_quadrature": mp.nstr(cubic, 68),
        "independent_harmonic_Mellin_eta": mp.nstr(eta, 68),
        "independent_bridge_absolute_error": mp.nstr(abs(cubic-predicted), 12),
        "arb_contains_independent_cubic_rounded_value": cubic_ball.contains(arb(mp.nstr(cubic, 69))),
        "arb_contains_independent_eta_rounded_value": eta_ball.contains(arb(mp.nstr(eta, 69))),
        "status": "The first route is interval certified; the quadratures are diagnostics.",
    })
    destination = Path(__file__).with_name("cubic_harmonic_verification.json")
    destination.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
