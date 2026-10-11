#!/usr/bin/env python3
"""Independent finite algebra and quadrature diagnostics for Section 4.

These are implementation checks, not substitutes for the analytic proofs.
Run from any directory; only the report path given by --output is written.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--dps", type=int, default=65)
    args = parser.parse_args()
    mp.mp.dps = args.dps
    exact = []
    numeric = []
    z, h = sp.symbols("z h", nonzero=True)
    for p in range(1, 8):
        for q in range(1, 8):
            rhs = sum(
                (-1)**q * sp.binomial(p+q-j-1, p-j)
                / h**(p+q-j) / (z+h)**j
                for j in range(1, p+1)
            ) + sum(
                (-1)**(q-j) * sp.binomial(p+q-j-1, q-j)
                / h**(p+q-j) / z**j
                for j in range(1, q+1)
            )
            assert sp.cancel(rhs - 1/((z+h)**p*z**q)) == 0
            exact.append(f"partial_fraction_{p}_{q}")
    bad = (1/(z+h)-1/z)/h - 1/((z+h)*z)
    assert sp.cancel(bad) != 0
    exact.append("reversed_sign_corruption_rejected")

    X, Y, Z2 = sp.symbols("X Y Z2")
    first = (X**2+Z2)/2 + (Y**2+Z2)/2 - Z2 - (X-Y)**2/2
    assert sp.expand(first-X*Y) == 0
    exact.append("mixed_zeroth_jet_polarization")

    def check(name, lhs, rhs, tolerance=None):
        tolerance = tolerance or mp.mpf(10)**(-args.dps+12)
        error = abs(lhs-rhs)
        scale = max(mp.mpf(1), abs(lhs), abs(rhs))
        assert error/scale < tolerance, (name, mp.nstr(error/scale, 12))
        numeric.append({
            "name": name,
            "lhs": mp.nstr(lhs, 35),
            "rhs": mp.nstr(rhs, 35),
            "relative_error": mp.nstr(error/scale, 10),
            "tolerance": mp.nstr(tolerance, 5),
        })

    twopi_i = 2*mp.pi*1j
    def green(theta, x):
        return mp.exp(-twopi_i*theta*x)/(1-mp.exp(-twopi_i*theta))
    def conv_green(theta, eta, x):
        return mp.quad(lambda t: green(theta,t)*green(eta,x-t), [0,x]) + \
               mp.quad(lambda t: green(theta,t)*green(eta,x-t+1), [x,1])

    for theta, eta in [(mp.mpf(1)/4,mp.mpf(3)/4),
                       (mp.mpf(-3)/10,mp.mpf(6)/5)]:
        for x in [mp.mpf(1)/7,mp.mpf(4)/5]:
            lhs = conv_green(theta,eta,x)
            rhs = (green(eta,x)-green(theta,x))/(twopi_i*(theta-eta))
            check(f"ordinary_resolvent_convolution_{theta}_{eta}_{x}",lhs,rhs)
    for x in [mp.mpf(1)/9,mp.mpf(5)/6]:
        check(f"half_twist_confluence_{x}",
              conv_green(mp.mpf('.5'),mp.mpf('.5'),x),
              mp.exp(-mp.pi*1j*x)*(x/2-mp.mpf(1)/4))

    theta, eta = mp.mpf(1)/4, mp.mpf(3)/4
    def rational_lerch(p, q, x):
        zz = mp.exp(-twopi_i*p/q)
        return -mp.exp(-twopi_i*p*x/q)/q * sum(
            zz**j*mp.digamma((x+j)/q) for j in range(q))
    for x in [mp.mpf(1)/11,mp.mpf(3)/7,mp.mpf(9)/10]:
        a_integral = twopi_i*mp.quad(lambda t: green(t,x),[eta,theta])
        a_digamma = rational_lerch(3,4,x)-rational_lerch(1,4,x)
        check(f"bounded_difference_digamma_{x}",a_integral,a_digamma)
    a0 = twopi_i*mp.quad(lambda t:green(t,0),[eta,theta])
    a1 = twopi_i*mp.quad(lambda t:green(t,1),[eta,theta])
    check("bounded_difference_jump",a0-a1,twopi_i*(theta-eta))

    # Peeling central modes keeps the principal branch correct. The test
    # compares unpeeled modes to direct complex powers, and separately
    # records a crossed mode that would fail a naive logarithm identity.
    theta, eta = mp.mpf('2.3'), mp.mpf('.2')
    alpha, beta = mp.mpc('.4','.2'), mp.mpc('-.7','.3')
    d = theta-eta
    for n in [-17,-8,7,21]:
        lt, le = twopi_i*(n+theta),twopi_i*(n+eta)
        lhs = mp.exp(alpha*mp.log(lt)+beta*mp.log(le))
        rhs = mp.fsum(mp.binomial(alpha,k)*(twopi_i*d)**k *
                      mp.exp((alpha+beta-k)*mp.log(le))
                      for k in range(200))
        check(f"lerch_tail_complex_orders_mode_{n}",lhs,rhs)
    n = -1
    phase = mp.log(twopi_i*(n+theta))-mp.log(twopi_i*(n+eta))
    check("crossed_mode_phase",mp.im(phase),mp.pi)

    # Direct Fourier coefficient of the bounded difference, computed from
    # an ordinary digamma representative, checks the distribution convention.
    def adiff(x):
        if x == 0:
            return a0
        return rational_lerch(3,4,x)-rational_lerch(1,4,x)
    for n in [-3,0,2]:
        lhs=mp.quad(lambda x:adiff(x)*mp.exp(-twopi_i*n*x),[0,mp.mpf('.5'),1])
        rhs=mp.log(twopi_i*(n+mp.mpf(1)/4))-mp.log(twopi_i*(n+mp.mpf(3)/4))
        check(f"bounded_difference_fourier_{n}",lhs,rhs)

    result={"suite":"unequal_twists","status":"passed",
            "working_decimal_digits":args.dps,
            "exact_assertions":len(exact),"exact_checks":exact,
            "numerical_comparisons":len(numeric),"numerical_checks":numeric,
            "evidence_scope":"Exact finite algebra and arbitrary-precision diagnostics; no interval certification or proof-assistant verification."}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("exact_checks","numerical_checks")},indent=2))


if __name__ == "__main__":
    main()
