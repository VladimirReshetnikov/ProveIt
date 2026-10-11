"""Independent double-pole finite-part quadrature for the repeated-pole theorem."""

import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 65


def F(r, x):
    return -mp.polygamma(r, x)


def interval_fp(ri, rj, offset, length):
    # The first factor is singular at t=0; the other is regular there.
    degree = ri+1
    leading = (-1)**ri * mp.factorial(ri)
    coeff = [F(rj+k, offset)/mp.factorial(k) for k in range(degree+5)]

    def integrand(t):
        other = F(rj, offset+t)
        if t < offset*mp.mpf("1e-10"):
            quotient = sum(coeff[k]*t**(k-degree) for k in range(degree, degree+5))
        else:
            quotient = (other-sum(coeff[k]*t**k for k in range(degree)))/t**degree
        return leading*quotient + F(ri, 1+t)*other

    numerical = mp.quad(integrand, [0, length/4, length/2, length])
    elementary = mp.mpf(0)
    for k in range(degree):
        q = degree-k
        primitive = mp.log(length) if q == 1 else length**(1-q)/(1-q)
        elementary += leading*coeff[k]*primitive
    return numerical+elementary


def pair_fp(r0, r1, e):
    return (interval_fp(r0, r1, e, 1-e)
            + interval_fp(r1, r0, 1-e, e))


report = []
reflection_checks = []
for es in ("0.03", "0.01", "0.003", "0.001"):
    e = mp.mpf(es)
    pair_sum = mp.mpf(0)
    for orders in ((1, 0), (0, 1)):
        c = pair_fp(*orders, e)
        pair_sum += c
        t = mp.log(e)/e**2 if orders == (1, 0) else (1-mp.log(e))/e**2
        row = {"orders": orders, "epsilon": es,
               "C_minus_T": mp.nstr(c-t, 40),
               "C_minus_T_minus_zeta2": mp.nstr(c-t-mp.zeta(2), 30)}
        report.append(row)
        print(json.dumps(row), flush=True)
    error = pair_sum-mp.pi**2/mp.sin(mp.pi*e)**2
    assert abs(error) < mp.mpf("1e-35")
    reflection_checks.append({"epsilon": es, "absolute_error": mp.nstr(abs(error), 12)})
Path(__file__).with_name("derivative_pair_verification.json").write_text(
    json.dumps({"working_decimal_digits": mp.mp.dps, "diagnostics": report,
                "independent_reflection_identity": reflection_checks}, indent=2)+"\n")
