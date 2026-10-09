#!/usr/bin/env python3
"""Exact finite algebraic checks supporting the Ford recurrence manuscript.

These checks verify displayed finite identities and rational inequalities.
They are not formal proofs of infinite series, spectral representations,
asymptotic remainders, or theorems quantified over all orders.

Run from the package root:
    python code/verify_symbolic.py
    python code/verify_symbolic.py --out data/symbolic_checks.json

The default output is rerun/symbolic_checks.json. Recorded data are preserved
unless an explicit --out path points into data/.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import sys
import time

import sympy as sp


class CheckRecorder:
    def __init__(self):
        self.checks = []

    def identity(self, name, computed, expected, context):
        residual = sp.simplify(sp.cancel(computed-expected))
        passed = bool(residual == 0)
        self.checks.append({"name": name, "kind": "exact finite identity",
                            "computed": str(computed), "expected": str(expected),
                            "residual": str(residual), "passed": passed,
                            "context": context})
        if not passed:
            raise RuntimeError(f"Identity failed: {name}: residual {residual}")

    def positive(self, name, rational_difference, context):
        value = sp.factor(rational_difference)
        if not value.is_Rational:
            raise TypeError(f"Expected an exact rational scalar for {name}: {value}")
        passed = bool(value > 0)
        self.checks.append({"name": name, "kind": "exact rational scalar inequality",
                            "positive_difference": str(value), "passed": passed,
                            "context": context})
        if not passed:
            raise RuntimeError(f"Rational inequality failed: {name}: {value}")


def check_density_taylor(recorder):
    s, v = sp.symbols("s V", real=True)
    p2, p3, p4 = sp.symbols("p2 p3 p4", real=True)
    f = 1/(v*v+sp.pi**2)
    correction = p2*s**2+p3*s**3+p4*s**4
    # Compute coefficients of the actual rational composition, independently
    # of the claimed derivative formulas below.
    b = sp.series(s/(1-sp.exp(-s)), s, 0, 5).removeO()
    direct = sp.series(b/((v+correction)**2+sp.pi**2), s, 0, 5).removeO().expand()
    derivative1 = sp.diff(f, v)
    derivative2 = sp.diff(f, v, 2)
    expected = [f, f/2, f/12+p2*derivative1,
                (p2/2+p3)*derivative1,
                -f/720+(p2/12+p3/2+p4)*derivative1+p2**2*derivative2/2]
    for r in range(5):
        recorder.identity(f"density_Q{r}", direct.coeff(s,r), expected[r],
                          "Coefficient of s^r in b(s) f(V+P(s)), through r=4.")
    recorder.identity("Bernoulli_prefactor_through_degree4", b,
                      1+s/2+s*s/12-s**4/720,
                      "Finite Taylor expansion of s/(1-exp(-s)).")
    hyperbolic = sp.series(s*s/(4*sp.sinh(s/2)**2)-1,s,0,6).removeO()
    recorder.identity("P_hyperbolic_part_through_degree4", hyperbolic,
                      -s*s/12+s**4/240,
                      "Checks the elementary contributions to p2 and p4.")


def check_logarithmic_coefficients(recorder):
    # U = log(Y)+EulerGamma for a Gamma(shape=2,rate=1) random variable.
    # The cumulants follow from polygamma values at 2. Construct moments
    # independently of the coefficient generator used by the numerical code.
    cumulants = {1: sp.Integer(1)}
    for k in range(2,5):
        cumulants[k] = (-1)**k*sp.factorial(k-1)*(sp.zeta(k)-1)
    moments = [sp.Integer(1)]
    for n in range(1,5):
        moments.append(sp.expand(sum(sp.binomial(n-1,k-1)*cumulants[k]*moments[n-k]
                                     for k in range(1,n+1))))
    moment_coefficients = []
    for k in range(5):
        value = sum((-1)**j*sp.binomial(k+1,2*j+1)*sp.pi**(2*j)*moments[k-2*j]
                    for j in range(k//2+1))
        moment_coefficients.append(sp.simplify(value))

    z = sp.symbols("z")
    exponent = -sum(sp.zeta(k)*z**k/k for k in range(2,5))
    generator = sp.series((1+z)*sp.exp(exponent),z,0,5).removeO().expand()
    explicit = [sp.Integer(1), sp.Integer(2), -sp.pi**2/2,
                -2*sp.pi**2-8*sp.zeta(3), sp.pi**4/12-40*sp.zeta(3)]
    for k in range(5):
        from_generator = sp.factorial(k+1)*generator.coeff(z,k)
        recorder.identity(f"c{k}_Gamma_log_moments_vs_generator", moment_coefficients[k],
                          from_generator,
                          "Independent finite Gamma log-moment and generator calculations.")
        recorder.identity(f"c{k}_displayed_constant", moment_coefficients[k], explicit[k],
                          "Checks the five displayed leading-sector constants.")
    return {"Gamma_shape": 2,
            "U_definition": "U=log(Y)+EulerGamma, Y~Gamma(shape=2,rate=1)",
            "cumulants": {str(k):str(v) for k,v in cumulants.items()},
            "moments_0_through_4": [str(sp.simplify(v)) for v in moments],
            "c0_through_c4": [str(v) for v in moment_coefficients]}


def check_product_identity(recorder):
    x = sp.symbols("x")
    for r in range(1,13):
        finite = sum((-x)**j for j in range(r))
        remainder = (-x)**r/(1+x)
        recorder.identity(f"alternating_geometric_remainder_order_{r}",
                          finite+remainder, 1/(1+x),
                          "Exact finite identity; no convergence hypothesis on |x|.")
    rho,t = sp.symbols("rho t")
    beta = rho/(1-rho)
    recorder.identity("product_denominator_substitution", (1-rho)*(1+beta*(1-t)),
                      1-rho*t,
                      "Substitution x=beta(1-t), beta=rho/(1-rho).")


def check_inverse_error_law(recorder):
    z,c,log_gamma = sp.symbols("z c log_gamma",real=True)
    alpha1,alpha2 = sp.symbols("alpha1 alpha2",real=True)
    minus_log_relative = sp.series(-sp.log(1+2*z-sp.pi**2*z*z/2),z,0,3).removeO()
    recorder.identity("inverse_input_logarithm",minus_log_relative,
                      -2*z+(sp.pi**2/2+2)*z*z,
                      "Finite logarithm algebra for the relative error factor.")

    # z=1/T. Terms of size T/B have already been separated analytically in
    # the paper; here we verify the algebra of the retained inverse powers.
    ax_minus_B = -2/z+2*sp.log(z)+2*c-log_gamma+alpha1*z+alpha2*z*z
    log_x = 1/z-c
    twice_log_log_x = -2*sp.log(z)+2*sp.series(sp.log(1-c*z),z,0,3).removeO()
    residual = ax_minus_B+2*log_x+twice_log_log_x+log_gamma \
        -2*z/(1-c*z)+(sp.pi**2/2+2)*z*z/(1-c*z)**2
    residual = sp.series(residual,z,0,3).removeO().expand()
    expected1 = 2*c+2
    expected2 = c*c+2*c-sp.pi**2/2-2
    recorder.identity("inverse_Tminus1_matching_equation", residual.coeff(z,1),
                      alpha1-expected1,
                      "Coefficient equation for the manuscript's T^-1 term.")
    recorder.identity("inverse_Tminus2_matching_equation", residual.coeff(z,2),
                      alpha2-expected2,
                      "Coefficient equation for the manuscript's T^-2 term.")
    recorder.identity("inverse_retained_residual_vanishes",
                      residual.subs({alpha1:expected1,alpha2:expected2}),0,
                      "The retained constant, T^-1, and T^-2 residuals cancel exactly.")
    return {"Tminus1_coefficient":str(expected1),"Tminus2_coefficient":str(expected2),
            "scope":"Coefficient matching after analytically separating O(T/B); no remainder proof here."}


def check_finite_bound_scalars(recorder):
    # The manuscript uses standard exponential/logarithm inequalities.
    # Record finite rational witnesses for their scalar constants, instead
    # of calling floating exp/log to label an inequality exact.
    exp4_lower = sum(sp.Rational(4)**k/sp.factorial(k) for k in range(10))
    recorder.positive("exp4_positive_partial_sum_exceeds_54",exp4_lower-54,
                      "With the positive exponential Taylor remainder, e^4>54 and 18e^-4<1/3.")
    exp1_partial = sum(sp.Rational(1,sp.factorial(k)) for k in range(5))
    exp1_upper = exp1_partial+sp.Rational(1,sp.factorial(5))/(1-sp.Rational(1,6))
    recorder.positive("exp1_geometric_tail_upper_below_11_over4",sp.Rational(11,4)-exp1_upper,
                      "After term 1/5!, later successive ratios are at most 1/6.")
    recorder.positive("exp1_geometric_tail_upper_below3",3-exp1_upper,
                      "Rational support for e<3, hence e^-1>1/3.")
    recorder.positive("exp4_from_exp1_upper_below64",64-exp1_upper**4,
                      "Rational support for e^4<64; n^-1/2<=1/64<e^-4 at n>=4096.")
    exp5_lower = sum(sp.Rational(5)**k/sp.factorial(k) for k in range(5))
    exp3_lower = sum(sp.Rational(3)**k/sp.factorial(k) for k in range(4))
    recorder.positive("exp5_partial_sum_exceeds64",exp5_lower-64,
                      "Rational support for log(64)<5.")
    recorder.positive("exp3_partial_sum_exceeds10",exp3_lower-10,
                      "Rational support for log(10)<3.")

    x = sp.symbols("x",real=True)
    recorder.identity("pi_integrand_upper_polynomial_remainder",
                      1/(1+x*x),1-x*x+x**4-x**6/(1+x*x),
                      "On 0<x<1 the remainder is negative; integrating gives a rational upper bound for pi.")
    pi_upper = 4*sp.integrate(1-x*x+x**4,(x,0,1))
    recorder.positive("pi_polynomial_upper_below4",4-pi_upper,
                      "The integrated upper polynomial is 52/15<4.")

    recorder.identity("density_lower_constant",sp.Rational(1,2)/(sp.Rational(16,9)+1),
                      sp.Rational(9,50),
                      "Combines h>=1/2, |R|<=4L/3 and pi<L.")
    recorder.identity("density_upper_constant",1/sp.Rational(2,3)**2,sp.Rational(9,4),
                      "Combines h<=1 and |R|>=2L/3.")
    ell_L = sp.symbols("L",real=True)
    recorder.identity("density_R_lower_margin",ell_L-sp.Rational(4,3)-sp.Rational(2,3)*ell_L,
                      (ell_L-4)/3,"Nonnegative for L>=4, by the stated assumption.")
    recorder.identity("density_R_upper_margin",sp.Rational(4,3)*ell_L-(ell_L+sp.Rational(4,3)),
                      (ell_L-4)/3,"Nonnegative for L>=4, by the stated assumption.")

    u = sp.symbols("u",real=True)
    recorder.identity("minus_log_linear_lower_derivative",
                      sp.diff(-u-sp.log(1-u),u),u/(1-u),
                      "Nonnegative on [0,1); supports -u-log(1-u)>=0.")
    recorder.identity("minus_log_quadratic_upper_derivative",
                      sp.diff(u*u+u+sp.log(1-u),u),u*(1-2*u)/(1-u),
                      "Nonnegative for 0<=u<=1/2; supports -u-log(1-u)<=u^2.")
    recorder.identity("binomial_exponential_bound_derivative",
                      sp.diff(u/(1-u)+sp.log(1-u),u),u/(1-u)**2,
                      "Supports log(1-u)>=-u/(1-u), used at u=1/n.")

    r = sp.symbols("r",positive=True)
    tail_log_gap = r-1/r-4*sp.log(r)-sp.log(1+r**-2)-2*sp.log(2*sp.log(r))
    derivative = 1+r**-2-4/r+2/(r*(r*r+1))-2/(r*sp.log(r))
    recorder.identity("upper_tail_log_gap_derivative",sp.diff(tail_log_gap,r),derivative,
                      "For r>=64, log(r)>1 gives a lower bound 1-6/r.")
    recorder.positive("upper_tail_derivative_lower_at64",1-sp.Rational(6,64),
                      "Positive uniform derivative lower bound for r>=64.")
    tail_at64_lower = 64-sp.Rational(1,64)-20-sp.Rational(1,4096)-6
    recorder.positive("upper_tail_log_gap_lower_at64",tail_at64_lower,
                      "Uses log64<5, log10<3, and log(1+1/4096)<=1/4096.")

    n = sp.symbols("n",positive=True)
    interval_integral = sp.integrate(u,(u,1/(2*n),1/n))
    recorder.identity("lower_bound_restricted_interval_integral",interval_integral,3/(8*n*n),
                      "Integral of u over [1/(2n),1/n].")
    recorder.identity("lower_bound_prefactor",sp.Rational(9,50)*sp.Rational(1,3)*sp.Rational(1,4)*sp.Rational(3,8),
                      sp.Rational(9,1600),"Product of the scalar factors in the lower bound.")
    recorder.identity("lower_bound_final_constant_margin",
                      sp.Rational(9,1600)/n**2-1/(200*n*(n+1)),
                      (n+9)/(1600*n*n*(n+1)),
                      "Strictly positive for n>0, by the displayed positive-factor form.")
    return {"exp4_lower_partial_degree":9,"exp4_lower_partial":str(exp4_lower),
            "exp1_upper_with_geometric_tail":str(exp1_upper),
            "pi_upper_polynomial_integral":str(pi_upper),
            "tail_log_gap_at64_rational_lower":str(tail_at64_lower)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,
                        default=Path(__file__).resolve().parents[1]/"rerun"/"symbolic_checks.json")
    args=parser.parse_args()
    start=time.monotonic()
    recorder=CheckRecorder()
    report={"status":"Exact finite checks only; not formal proofs of infinite or asymptotic statements.",
            "python":platform.python_version(),"sympy":sp.__version__,
            "python_optimization_level":sys.flags.optimize}
    check_density_taylor(recorder)
    report["independent_Gamma_log_moments"]=check_logarithmic_coefficients(recorder)
    check_product_identity(recorder)
    report["inverse_error_law"]=check_inverse_error_law(recorder)
    report["rational_scalar_witnesses"]=check_finite_bound_scalars(recorder)
    report["checks"]=recorder.checks
    report["check_count"]=len(recorder.checks)
    report["all_checks_passed"]=all(check["passed"] for check in recorder.checks)
    if not report["all_checks_passed"]:
        raise RuntimeError("A symbolic check failed.")
    report["elapsed_seconds"]=time.monotonic()-start
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"check_count":report["check_count"],"all_checks_passed":True,
                      "output":str(args.out.resolve()),"seconds":report["elapsed_seconds"]},indent=2))


if __name__=="__main__":
    main()
