#!/usr/bin/env python3
"""Exact finite algebra checks for mixed poles and the cubic-harmonic bridge.

Requirements: Python 3 and SymPy.  Run from any working directory.  The JSON
result is written beside this script.  There are no floating-point checks.
These finite certificates do not certify convergence or Mellin continuation.
"""
from pathlib import Path
import json
import sympy as S

eps = S.Symbol("eps")
x = S.Symbol("x", positive=True)
G = S.Symbol("gamma")
Z = {k: S.Symbol("zeta_"+str(k)) for k in range(2, 7)}
DEGREE = 6


def harmonic(n, r=1):
    return sum((S.Rational(1, k**r) for k in range(1, n+1)), S.Integer(0))


def exp_coefficients(log_coeffs, degree=DEGREE):
    """Coefficients of exp(sum(lambda[k]*eps**k)), by its differential eq."""
    out = [S.Integer(1)]
    for n in range(1, degree+1):
        out.append(S.expand(sum((k*log_coeffs[k]*out[n-k]
                                 for k in range(1, n+1)), S.Integer(0))/n))
    return out


def polynomial_coefficients(f, degree=DEGREE):
    f = S.expand(f)
    return [f.coeff(eps, n) for n in range(degree+1)]


def prescribed_gamma_coefficients(m):
    """Generalized-harmonic exponential formula stated in the manuscript."""
    if m >= 1:
        N = m-1
        log_coeffs = {1: G-harmonic(N)}
        log_coeffs.update({k: (-1)**(k+1)*(Z[k]-harmonic(N,k))/k
                          for k in range(2, DEGREE+1)})
        return [S.expand(c/S.factorial(N)) for c in exp_coefficients(log_coeffs)]
    N = -m
    log_coeffs = {1: G-harmonic(N)}
    log_coeffs.update({k: ((-1)**(k+1)*Z[k]-harmonic(N,k))/k
                      for k in range(2, DEGREE+1)})
    c = exp_coefficients(log_coeffs)
    return [S.Integer(0)] + [S.expand((-1)**N*S.factorial(N)*c[n-1])
                            for n in range(1, DEGREE+1)]


def recurrence_gamma_coefficients(m):
    """Independent integer-shift construction from Gamma(z+1)=z Gamma(z)."""
    log_base = {1: G}
    log_base.update({k: (-1)**(k+1)*Z[k]/k
                     for k in range(2, DEGREE+1)})
    base = exp_coefficients(log_base)  # reciprocal Gamma(1+eps)
    if m >= 1:
        denominator = S.Poly(S.prod(eps+k for k in range(1,m)), eps)
        out = []
        for n in range(DEGREE+1):
            correction = sum((denominator.nth(k)*out[n-k]
                              for k in range(1,n+1)), S.Integer(0))
            out.append(S.expand((base[n]-correction)/denominator.nth(0)))
        return out
    N = -m
    numerator = eps*S.prod(eps-k for k in range(1,N+1))
    return polynomial_coefficients(numerator*sum(c*eps**n for n,c in enumerate(base)))


def main():
    gamma_rows, direct_gamma = [], {}
    gamma_formal_checks = gamma_direct_checks = 0
    actual_constants = {G: S.EulerGamma, **{Z[k]: S.zeta(k) for k in Z}}
    for m in (1,2,5,0,-1,-4):
        target = prescribed_gamma_coefficients(m)
        recurrence = recurrence_gamma_coefficients(m)
        for a,b in zip(target, recurrence):
            assert S.expand(a-b) == 0, ("Gamma recurrence",m,a,b)
            gamma_formal_checks += 1
        # A separate SymPy special-function series verifies degrees 0 through 4.
        direct = S.series(1/S.gamma(m+eps),eps,0,5).removeO().expand()
        direct_gamma[m] = direct
        for n in range(5):
            assert S.simplify(direct.coeff(eps,n)-target[n].subs(actual_constants)) == 0
            gamma_direct_checks += 1
        gamma_rows.append({
            "center":m,
            "formal_coefficients_through_degree_6":[str(c) for c in target],
            "integer_shift_recurrence_passed":True,
            "direct_sympy_series_through_degree_4_passed":True,
        })

    # Derive the needed kernel coefficients from the elementary Li_0 and Li_1
    # expressions, independently of the manuscript's displayed local expansion.
    li0 = S.series(S.exp(-x)/(1-S.exp(-x)),x,0,2).removeO()
    li1 = S.series(-S.log(1-S.exp(-x)),x,0,3).removeO()
    log_x = S.Symbol("log_x")
    kernel = S.expand(li0*li1**2).subs(S.log(x),log_x)
    expected = {
        -1:[S.Integer(0),S.Integer(0),S.Integer(1)],
        0:[S.Integer(0),-S.Integer(1),-S.Rational(1,2)],
        1:[S.Rational(1,4),S.Rational(7,12),S.Rational(1,12)],
    }
    local_coefficients = {}
    kernel_checks = 0
    for power, row in expected.items():
        for log_power, value in enumerate(row):
            got = S.expand(kernel).coeff(x,power).coeff(log_x,log_power)
            assert got == value, ("kernel",power,log_power,got,value)
            local_coefficients[(power,log_power)] = got
            kernel_checks += 1

    desired_pp = {
        1:2/eps**3+2*S.EulerGamma/eps**2+(S.EulerGamma**2-S.zeta(2))/eps,
        0:-1/eps**2+(1-S.EulerGamma)/eps,
        -1:-1/(6*eps**2)+(S.Rational(3,4)-S.EulerGamma/6)/eps,
    }
    principal_rows = []
    for m in (1,0,-1):
        raw_mellin = sum((-1)**b*S.factorial(b)*local_coefficients[(-m,b)]
                         /eps**(b+1) for b in range(3))
        local = S.expand(raw_mellin*direct_gamma[m])
        principal = sum(local.coeff(eps,k)*eps**k for k in (-3,-2,-1))
        assert S.simplify(principal-desired_pp[m]) == 0
        principal_rows.append({
            "center":m,
            "epsilon_definition":"C minus center",
            "raw_mellin_principal_part":str(raw_mellin),
            "normalized_principal_part":str(S.expand(principal)),
            "passed":True,
        })

    # All harmonic quantities are exact rationals.  Euler's constant and zeta(2)
    # remain algebraically independent formal symbols throughout these checks.
    def a(n):
        return Z[2]+harmonic(n,2)-(harmonic(n)-G)**2

    bridge_rows = []
    for N in range(1,13):
        h, h2, h3 = harmonic(N), harmonic(N,2), harmonic(N,3)
        sn = sum((harmonic(n)/n**2 for n in range(1,N+1)), S.Integer(0))
        lhs = sum((a(n)/n for n in range(1,N+1)), S.Integer(0))
        rhs = ((Z[2]-G**2)*h+G*(h**2+h2)-h**3/3+h*h2-2*sn+4*h3/3)
        assert S.expand(lhs-rhs) == 0, ("harmonic sum",N)
        assert S.expand(a(N)-a(N-1)+2*(harmonic(N-1)-G)/N) == 0
        # The other summation-by-parts identity is tested with independent
        # formal log(n) symbols and log(1)=0, so no numerical logarithms enter.
        logs = [None,S.Integer(0)]+list(S.symbols("L2:"+str(N+2)))
        log_lhs = sum((a(n)*(logs[n+1]-logs[n]) for n in range(1,N+1)),S.Integer(0))
        log_rhs = a(N)*logs[N+1]+2*sum(((harmonic(n-1)-G)*logs[n]/n
                                     for n in range(1,N+1)),S.Integer(0))
        assert S.expand(log_lhs-log_rhs) == 0, ("log summation by parts",N)
        bridge_rows.append({
            "N":N,
            "sum_a_n_over_n":str(S.expand(lhs)),
            "reciprocal_sum_identity_passed":True,
            "finite_difference_passed":True,
            "formal_log_summation_by_parts_passed":True,
        })

    counts = {
        "formal_gamma_coefficient_checks":gamma_formal_checks,
        "direct_sympy_gamma_coefficient_checks":gamma_direct_checks,
        "local_kernel_coefficient_checks":kernel_checks,
        "normalized_principal_part_checks":len(principal_rows),
        "finite_harmonic_algebra_checks":3*len(bridge_rows),
    }
    result = {
        "status":"passed",
        "arithmetic":"exact symbolic and rational SymPy arithmetic",
        "sympy_version":S.__version__,
        "checks":counts,
        "total_exact_checks":sum(counts.values()),
        "formal_constant_convention":"gamma,zeta_2,...,zeta_6 are independent symbols in formal checks; direct SymPy checks use actual EulerGamma and zeta values.",
        "gamma_coefficients":gamma_rows,
        "local_kernel_coefficients":[{"x_power":v,"log_power":b,"coefficient":str(c)}
                                     for (v,b),c in local_coefficients.items()],
        "principal_parts":principal_rows,
        "cubic_harmonic_bridge":bridge_rows,
        "limitations":"These tests certify finite algebra only. Mellin continuation, local remainder estimates, and infinite-series convergence require the analytic arguments in the article.",
    }
    destination = Path(__file__).resolve().with_name("local_coefficients_checks.json")
    destination.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":result["status"],"checks":counts,
                      "total_exact_checks":result["total_exact_checks"]},indent=2))


if __name__ == "__main__":
    main()
