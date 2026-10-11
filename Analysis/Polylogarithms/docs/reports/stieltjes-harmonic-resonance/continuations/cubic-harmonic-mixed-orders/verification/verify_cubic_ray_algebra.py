#!/usr/bin/env python3
"""Exact symbolic certificates for cubic Tornheim rays and curved paths.

This is a self-contained algebra check.  It does not import another
workspace file, use floating-point inputs, or numerically approximate
special-function constants.  The constants are independent SymPy symbols.
The output JSON is written beside this script and is deterministic.

The analytic justification of the local meromorphic decomposition and
the prescribed one-variable restrictions belongs to the accompanying
article.  This script verifies its finite Taylor algebra.
"""

import json
from pathlib import Path

import sympy as sp


DEGREE = 3
a, b, c = sp.symbols("a b c")
gamma, log2pi, zeta2, zeta3 = sp.symbols("gamma L zeta2 zeta3")
z00, z000 = sp.symbols("zeta2_0 zeta3_0")
zm1, zm2, zm3 = sp.symbols("zeta1_m1 zeta2_m1 zeta3_m1")
omega3, anchor_j, kappa = sp.symbols("Omega3 J3 kappa")
h20, h11, h10c, h02 = sp.symbols("h20 h11 h10c h02")
alpha = sp.symbols("alpha_a alpha_b alpha_c")
beta = sp.symbols("beta_a beta_b beta_c")
delta = sp.symbols("delta_a delta_b delta_c")
variables = (a, b, c)

h0 = zm1 + log2pi/2 - 5*gamma/12
ha = (log2pi**2/8-z00/2+gamma*zm1-gamma*log2pi/4
      -(gamma**2+zeta2)/24)
hc = ((zm2-z00)/2-gamma*(zm1+log2pi/2)
      +5*(gamma**2+zeta2)/24)


def add(*arrays):
    return [sp.Add(*(x[k] for x in arrays)) for k in range(DEGREE+1)]


def scale(array, multiplier):
    return [multiplier*x for x in array]


def multiply(*arrays):
    result = [sp.Integer(1)] + [sp.Integer(0)]*DEGREE
    for other in arrays:
        result = [sp.Add(*(result[j]*other[k-j] for j in range(k+1)))
                  for k in range(DEGREE+1)]
    return result


def analytic_polynomial(coefficients, argument):
    result = [sp.Integer(0)]*(DEGREE+1)
    power = [sp.Integer(1)] + [sp.Integer(0)]*DEGREE
    for coefficient in coefficients:
        result = add(result, scale(power, coefficient))
        power = multiply(power, argument)
    return result


def divide(numerator, denominator):
    """Taylor division with nonzero denominator constant coefficient."""
    quotient = []
    for k in range(DEGREE+1):
        cross = sp.Add(*(denominator[j]*quotient[k-j]
                         for j in range(1, k+1)))
        quotient.append((numerator[k]-cross)/denominator[0])
    return quotient


ZETA_ZERO = [-sp.Rational(1, 2), -log2pi/2, z00/2, z000/6]
ZETA_MINUS_ONE = [-sp.Rational(1, 12), zm1, zm2/2, zm3/6]
GAMMA_MINUS = [1, gamma, (gamma**2+zeta2)/2,
               (gamma**3+3*gamma*zeta2+2*zeta3)/6]
RECIP_GAMMA_PLUS = [1, gamma, (gamma**2-zeta2)/2,
                    (gamma**3-3*gamma*zeta2+2*zeta3)/6]


def ray_taylor(aa, bb, cc, quadratic_h=True):
    aa, bb, cc = map(sp.sympify, (aa, bb, cc))
    arg_a = [0, aa, 0, 0]
    arg_b = [0, bb, 0, 0]
    arg_c = [0, cc, 0, 0]
    polynomial_h = [h0, ha*(aa+bb)+hc*cc, 0, 0]
    if quadratic_h:
        polynomial_h[2] = (h20*(aa**2+bb**2)+h11*aa*bb
                           +h10c*(aa+bb)*cc+h02*cc**2)
    inside = add(
        multiply(analytic_polynomial(ZETA_ZERO, arg_a),
                 analytic_polynomial(ZETA_ZERO, arg_b)),
        scale(multiply(analytic_polynomial(GAMMA_MINUS, arg_a),
                       analytic_polynomial(ZETA_MINUS_ONE, arg_b)),
              -cc/(aa+cc)),
        scale(multiply(analytic_polynomial(GAMMA_MINUS, arg_b),
                       analytic_polynomial(ZETA_MINUS_ONE, arg_a)),
              -cc/(bb+cc)),
        multiply(arg_c, polynomial_h),
    )
    result = multiply(analytic_polynomial(RECIP_GAMMA_PLUS, arg_c), inside)
    return [sp.factor(result[j])*sp.factorial(j) for j in range(DEGREE+1)]


def curve_kernel_taylor(path_coefficients, quadratic_h=False):
    """Direct composition of K (or its quadratic-H extension).

    Each input array lists the t, t^2, t^3, t^4 coefficients.  The
    quotient C/(A+C) is evaluated after cancelling the common t.
    """
    aa, bb, cc = path_coefficients
    arg_a = [0]+list(aa[:3])
    arg_b = [0]+list(bb[:3])
    arg_c = [0]+list(cc[:3])
    quotient_ac = divide(list(cc), [aa[j]+cc[j] for j in range(4)])
    quotient_bc = divide(list(cc), [bb[j]+cc[j] for j in range(4)])
    polynomial_h = add(
        [h0, 0, 0, 0], scale(add(arg_a, arg_b), ha), scale(arg_c, hc)
    )
    if quadratic_h:
        polynomial_h = add(
            polynomial_h,
            scale(add(multiply(arg_a, arg_a), multiply(arg_b, arg_b)), h20),
            scale(multiply(arg_a, arg_b), h11),
            scale(multiply(add(arg_a, arg_b), arg_c), h10c),
            scale(multiply(arg_c, arg_c), h02),
        )
    inside = add(
        multiply(analytic_polynomial(ZETA_ZERO, arg_a),
                 analytic_polynomial(ZETA_ZERO, arg_b)),
        scale(multiply(quotient_ac,
                       analytic_polynomial(GAMMA_MINUS, arg_a),
                       analytic_polynomial(ZETA_MINUS_ONE, arg_b)), -1),
        scale(multiply(quotient_bc,
                       analytic_polynomial(GAMMA_MINUS, arg_b),
                       analytic_polynomial(ZETA_MINUS_ONE, arg_a)), -1),
        multiply(arg_c, polynomial_h),
    )
    return multiply(analytic_polynomial(RECIP_GAMMA_PLUS, arg_c), inside)


def differential(expression, direction):
    return sp.Add(*(component*sp.diff(expression, variable)
                    for component, variable in zip(direction, variables)))


def exact_zero(expression):
    return sp.factor(sp.together(expression)) == 0


def main():
    anchors = [ray_taylor(*direction)[3]
               for direction in ((0, 0, 1), (1, 0, 1), (1, 1, 1), (1, 0, 2))]
    targets = [zm3-z000, -sp.Rational(9, 2)*z000-sp.Rational(3, 2)*log2pi*z00,
               omega3, anchor_j]
    solutions = sp.solve([lhs-rhs for lhs, rhs in zip(anchors, targets)],
                         (h20, h11, h10c, h02), dict=True)
    assert len(solutions) == 1
    solution = solutions[0]
    actual = ray_taylor(a, b, c)[3].subs(solution)
    j_to_kappa = kappa-sp.Rational(35, 2)*z000-6*log2pi*z00+9*zm3
    actual = actual.subs(anchor_j, j_to_kappa)
    sigma = a+b+c
    shape_b = c*(c*c+a*b-a*a-b*b)/((a+c)*(b+c))
    shape_d = a*a+b*b-c*(a+b)
    expected = (
        a*b*c*omega3-c*shape_d*kappa/2
        +(8*a*b*c-((a+c)**3+(b+c)**3)/2)*z000
        -sp.Rational(3, 2)*((a+b)*(a*b+c*c)-4*a*b*c)*log2pi*z00
        +sigma*sigma*shape_b*zm3
    )
    generic_residual = sp.factor(actual-expected)
    assert generic_residual == 0
    checks = {"generic_cubic_ray_reduction": True}

    def record(name, lhs, rhs=0):
        passed = exact_zero(lhs-rhs)
        checks[name] = bool(passed)
        assert passed, name

    record("axis_0_0_c", expected.subs({a: 0, b: 0}), c**3*(zm3-z000))
    record("product_slice_C_zero", expected.subs(c, 0),
           -(a**3+b**3)*z000/2-sp.Rational(3, 2)*a*b*(a+b)*log2pi*z00)
    record("symmetric_equal_slice_A_C", expected.subs({b: 0, c: a}),
           -sp.Rational(9, 2)*a**3*z000-sp.Rational(3, 2)*a**3*log2pi*z00)
    slice_ac = expected.subs(b, 0)
    slice_ca = slice_ac.xreplace({a: c, c: a})
    record("symmetric_slice_shuffle", slice_ac+slice_ca,
           -((a**3+c**3)/2+(a+c)**3)*z000
           -sp.Rational(3, 2)*a*c*(a+c)*log2pi*z00)
    record("diagonal_scaling", expected.subs({b: a, c: a}), a**3*omega3)
    record("exchange_A_B", expected, expected.xreplace({a: b, b: a}))
    record("anchor_1_0_2", expected.subs({a: 1, b: 0, c: 2}), j_to_kappa)
    degree_operator = sum(v*sp.diff(expected, v) for v in variables)
    record("cubic_homogeneity", degree_operator, 3*expected)

    ray_low = ray_taylor(a, b, c, quadratic_h=False)
    f0, f1, f2 = ray_low[:3]
    for order, fj in enumerate((f0, f1, f2)):
        record("f%d_homogeneity" % order,
               sum(v*sp.diff(fj, v) for v in variables), order*fj)

    eps = sp.symbols("epsilon")
    perturbed = ((a, 0, 0, eps), (b, 0, 0, 0), (c, 0, 0, 0))
    straight = ((a, 0, 0, 0), (b, 0, 0, 0), (c, 0, 0, 0))
    straight_kernel = curve_kernel_taylor(straight)[3]
    fourth_correction = 6*(curve_kernel_taylor(perturbed)[3]-straight_kernel)
    record("fourth_jet_perturbation", fourth_correction,
           -c*eps/(2*(a+c)**2))
    record("fourth_jet_diagonal_example", fourth_correction.subs({a: 1, b: 1, c: 1}),
           -eps/8)

    # Keep every acceleration, cubic jet and fourth jet symbolic.  Compare
    # a direct formal quotient expansion against the differential formula.
    full_path = tuple((variables[j], alpha[j], beta[j], delta[j])
                      for j in range(3))
    direct_correction = 6*(curve_kernel_taylor(full_path)[3]-straight_kernel)
    differential_correction = (
        6*differential(f0, delta)
        +6*differential(differential(f0, alpha), beta)
        +differential(differential(differential(f0, alpha), alpha), alpha)
        +6*differential(f1, beta)
        +3*differential(differential(f1, alpha), alpha)
        +3*differential(f2, alpha)
    )
    # Coefficientwise cancellation avoids creating an unnecessarily huge
    # common denominator for the complete polynomial in nine path jets.
    difference_poly = sp.Poly(sp.expand(direct_correction-differential_correction),
                              *alpha, *beta, *delta)
    monomial_checks = [exact_zero(coefficient)
                       for _monomial, coefficient in difference_poly.terms()]
    assert all(monomial_checks)
    checks["generic_curve_differential_identity"] = True

    unknown_difference = 6*(
        curve_kernel_taylor(full_path, quadratic_h=True)[3]
        -curve_kernel_taylor(full_path)[3]
        -curve_kernel_taylor(straight, quadratic_h=True)[3]
        +straight_kernel
    )
    record("quadratic_H_contribution_depends_only_on_tangent", unknown_difference)
    report = {
        "status": "PASS",
        "arithmetic": "exact symbolic rational arithmetic; all zeta constants remain formal symbols",
        "sympy_version": sp.__version__,
        "assumptions": "(a+c)(b+c) != 0; path arrays contain Taylor coefficients [t^j]A(t), so raw jth derivatives are j! times these coordinates",
        "notation": {
            "zeta2_0": "zeta''(0)",
            "zeta3_0": "zeta'''(0)",
            "zeta1_m1": "zeta'(-1)",
            "zeta2_m1": "zeta''(-1)",
            "zeta3_m1": "zeta'''(-1)",
            "Omega3": "d^3/dt^3 T(t,t,t) at t=0",
            "J3": "d^3/dt^3 T(t,0,2t) at t=0",
            "kappa": "J3 + 35*zeta'''(0)/2 + 6*L*zeta''(0) - 9*zeta'''(-1)",
        },
        "generic_ray_exact_residual": str(generic_residual),
        "generic_ray_third_derivative": str(expected),
        "H_quadratic_coefficients": {str(key): str(sp.factor(value))
                                     for key, value in sorted(solution.items(), key=lambda item: str(item[0]))},
        "ray_low_jets": {"f%d" % j: str(sp.factor(ray_low[j])) for j in range(3)},
        "curve_residual_polynomial_terms_checked": len(monomial_checks),
        "curve_symbolic_path_jet_parameters": len(alpha+beta+delta),
        "curve_exact_residual": "0",
        "fourth_jet_exact_change": str(sp.factor(fourth_correction)),
        "checks": checks,
        "all_checks_pass": all(checks.values()),
    }
    destination = Path(__file__).with_name("cubic_ray_algebra_verification.json")
    destination.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": report["status"],
                      "exact_checks": len(checks),
                      "curve_symbolic_path_jet_parameters": len(alpha+beta+delta),
                      "generic_ray_exact_residual": str(generic_residual),
                      "curve_exact_residual": "0",
                      "fourth_jet_exact_change": str(sp.factor(fourth_correction))},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
