#!/usr/bin/env python3
"""Independent numerical checks of the half-twist identity and source repair.

These are floating-point diagnostics, not interval certificates.  The
half-twist integral is evaluated using digamma/polygamma functions; its
comparison value uses Hurwitz Stieltjes constants, and the half-shift
specialization uses log Gamma independently. Endpoint cancellations are
removed analytically before quadrature.
"""
from pathlib import Path
import json
import platform
import mpmath as mp

mp.mp.dps = 60
OUT = Path(__file__).with_suffix(".json")
checks = []

def record(name, lhs, rhs, tolerance="1e-45", **params):
    residual = abs(lhs-rhs)
    scaled = residual/(1+abs(rhs))
    passed = scaled < mp.mpf(tolerance)
    checks.append(dict(name=name, parameters=params,
                       lhs=mp.nstr(lhs, 58), rhs=mp.nstr(rhs, 58),
                       absolute_residual=mp.nstr(residual, 12),
                       scaled_residual=mp.nstr(scaled, 12),
                       tolerance=tolerance, passed=bool(passed)))
    assert passed, (name, residual, scaled)

def f0(x):
    return (mp.digamma((x+1)/2)-mp.digamma(x/2))/2

def f1(x):
    return (mp.log(2)*(-mp.digamma(x/2)+mp.digamma((x+1)/2))
            +mp.stieltjes(1,x/2)-mp.stieltjes(1,(x+1)/2))/2

def half_twist_integral(a):
    fa = f0(a)
    coeff = [(mp.polygamma(k,(a+1)/2)-mp.polygamma(k,a/2))
             / (2**(k+1)*mp.factorial(k)) for k in range(19)]
    eta = [mp.log(2)] + [
        (1-mp.power(2,-j))*mp.zeta(j+1) for j in range(1,19)]
    def integrand(x):
        if x < mp.mpf("1e-5"):
            b = mp.fsum(coeff[k]*(-x)**k for k in range(19))
            quotient = mp.fsum((-1)**k*coeff[k]*x**(k-1)
                               for k in range(1,19))
            regular = -mp.fsum(eta[j]*(-x)**j for j in range(19))
        else:
            b = f0(a-x)
            quotient = (b-fa)/x
            regular = f0(x)-1/x
        return quotient + regular*b-fa/(a-x)
    first = 2*mp.quad(integrand,[0,mp.mpf("1e-5"),a/4,a/2])
    wrapped = mp.quad(lambda x:f0(x)*f0(1+a-x),[a,(a+1)/2,1])
    return first-wrapped+2*fa*mp.log(a)

for astr in ["0.25","0.5","0.73"]:
    a=mp.mpf(astr)
    value=half_twist_integral(a)
    record("half_twist_convergent_integral",value,2*f1(a),a=astr)
    if a==mp.mpf("0.5"):
        gamma_value=mp.pi*(4*mp.loggamma(mp.mpf("0.25"))-mp.euler
                          -3*mp.log(2*mp.pi))
        record("half_twist_quarter_gamma_value",value,gamma_value,a=astr)

def clausen2(x):
    return mp.im(mp.polylog(2,mp.exp(1j*x)))

for lamstr in ["-0.75","-0.5","0.25","0.8"]:
    lam=mp.mpf(lamstr)
    theta=mp.asin(lam)
    lhs=mp.quad(lambda x:mp.atanh(lam*mp.sin(x)),[0,mp.pi/4,mp.pi/2])
    rhs=(theta*mp.log(abs(mp.tan(theta/2)))+2*clausen2(theta)
         -clausen2(2*theta)/2)
    record("corrected_arctanh_identity",lhs,rhs,lambda_value=lamstr)
    if lam==mp.mpf("-0.5"):
        printed=(theta*mp.log(mp.tan(theta/2))+2*clausen2(theta)
                 -clausen2(2*theta)/2)
        record("exact_spurious_imaginary_term",printed-lhs,
               -1j*mp.pi**2/6,lambda_value=lamstr)

report = dict(
    description="Independent digamma quadrature, Hurwitz-Stieltjes and Gamma comparisons; branch audit",
    status="passed", decimal_precision=mp.mp.dps,
    environment=dict(python=platform.python_version(),mpmath=mp.__version__),
    numerical_proof=False, certified_intervals=False,
    endpoint_method="19-term analytic Taylor quotient below x=1e-5; ordinary smooth quadrature elsewhere",
    count=len(checks), checks=checks,
    maximum_scaled_residual=mp.nstr(max(mp.mpf(x["scaled_residual"]) for x in checks),12))
OUT.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:report[k] for k in ("status","count","decimal_precision","maximum_scaled_residual")}))

