#!/usr/bin/env python3
"""Exact higher-order certificates for the five-point extremal profile.

The symbolic checks verify the displayed algebra and critical-point
expansions.  The optional high-precision calculation checks a stationary
branch, not the global maximum or an analytic radius of convergence.
Neither computation substitutes for the compactness and implicit-function
arguments in the article.
"""
from pathlib import Path
import argparse
import json

import sympy as sp


def symbolic_checks():
    z, x, k, q = sp.symbols("z x k q", positive=True)
    t, theta, phi = sp.symbols("t theta phi", real=True)
    R = sp.symbols("R", positive=True)
    q_value = sp.Pow(2, sp.Rational(-3, 4))
    coefficients = sp.symbols("c1:5")
    X = 1 + sum(coefficients[j - 1] * z**j for j in range(1, 5))
    norm_polynomial = X**4 + 2*z*X**3 + 6*z**2*X**2 + 2*z**3*X + z**4 - 1
    solved = {}
    for degree in range(1, 5):
        coefficient = sp.expand(norm_polynomial).coeff(z, degree).subs(solved)
        solved[coefficients[degree - 1]] = sp.solve(
            coefficient, coefficients[degree - 1])[0]
    X = sp.expand(X.subs(solved))
    expected_X = (1-z/2-sp.Rational(9, 8)*z**2
                  +sp.Rational(3, 4)*z**3+sp.Rational(39, 128)*z**4)
    assert X == expected_X

    rho_squared = q*x*X.subs(z, k**2*x/q)
    b = k*x
    fixed_objective = (24*(rho_squared**2+b**4)+16*rho_squared**2*b
                       +96*rho_squared**2*b**2+48*rho_squared*b**4
                       +32*rho_squared**2*b**3+x**4)
    objective_coefficients = [sp.factor(sp.expand(fixed_objective).coeff(x, j))
                              for j in range(2, 7)]
    H0_fixed, H2_fixed, H4_fixed, H6_fixed = objective_coefficients[1:]
    assert sp.simplify(objective_coefficients[0]-24*q**2) == 0
    assert sp.simplify(H0_fixed-(-24*q*k**2+16*q**2*k)) == 0
    assert sp.simplify(H2_fixed-(1-24*k**4-16*q*k**3+96*q**2*k**2)) == 0
    assert sp.simplify(H4_fixed-(63*k**6/q-32*k**5-48*q*k**4+32*q**2*k**3)) == 0
    assert sp.simplify(H6_fixed-(27*k**8/q**2+42*k**7/q-216*k**6-32*q*k**5)) == 0

    A = 1+sp.cos(phi)**2
    H0 = -24*q*A*k**2+16*q**2*k*sp.cos(theta)
    H2 = (1+24*(A**2-2)*k**4-16*q*A*k**3*sp.cos(theta)
          +24*(3+sp.cos(2*theta))*q**2*k**2)
    H3 = (16*sp.sqrt(q)*k**4*sp.cos(phi-theta)
          +48*q**sp.Rational(3, 2)*k**3
          *(sp.cos(2*theta-phi)+sp.cos(phi)))
    coordinates = (k, theta, phi)
    at_limit = {k: q/3, theta: 0, phi: sp.pi/2}
    hessian = sp.simplify(sp.hessian(H0, coordinates).subs(at_limit))
    expected_hessian = sp.diag(-48*q, -16*q**3/3, -16*q**3/3)
    assert hessian == expected_hessian
    grad_H2 = sp.Matrix([sp.diff(H2, v) for v in coordinates]).subs(at_limit)
    grad_H3 = sp.Matrix([sp.diff(H3, v) for v in coordinates]).subs(at_limit)
    y2 = sp.simplify(-hessian.inv()*grad_H2)
    y3 = sp.simplify(-hessian.inv()*grad_H3)
    assert y2 == sp.Matrix([31*q**2/27, 0, 0])
    assert y3 == sp.Matrix([0, 19*q**sp.Rational(3, 2)/27,
                           -19*q**sp.Rational(3, 2)/27])

    k0 = q/3
    K8 = sp.simplify(H2_fixed.subs(k, k0).subs(q, q_value))
    K10 = sp.factor(H4_fixed.subs(k, k0)
                    +sp.diff(H2_fixed, k).subs(k, k0)**2/(96*q))
    fixed_twelfth = sp.factor(H6_fixed.subs(k, k0))
    amplitude_twelfth = sp.factor(
        (y2[0]*sp.diff(H4_fixed, k)
         +sp.Rational(1, 2)*y2[0]**2*sp.diff(H2_fixed, k, 2)).subs(k, k0))
    phase_twelfth = sp.factor(-(grad_H3.T*hessian.inv()*grad_H3)[0]/2)
    K12 = sp.factor(fixed_twelfth+amplitude_twelfth+phase_twelfth)
    assert K8 == sp.Rational(20, 9)
    assert sp.simplify(K10.subs(q, q_value)-869*q_value/216) == 0
    assert sp.simplify(K12.subs(q, q_value)
                       -sp.Rational(65759, 5832)*sp.Pow(2, sp.Rational(-3, 2))) == 0

    psi = phi-theta
    norm = (8*R**4+16*(1+sp.cos(phi)**2)*R**3*k**2*t**2
            +48*R**2*k**4*t**4
            +16*(1+sp.cos(2*theta-phi)**2)*R*k**6*t**6+8*k**8*t**8)
    objective = (1+24*(t**4*R**2+t**8*k**4)
                 +16*(t**6*R**2*k*sp.cos(theta)
                      +t**9*sp.sqrt(R)*k**4*sp.cos(psi))
                 +24*((3+sp.cos(2*theta))*t**8*R**2*k**2
                      +(3+sp.cos(2*psi))*t**10*R*k**4
                      +2*t**9*R**sp.Rational(3, 2)*k**3
                      *(sp.cos(phi)+sp.cos(2*theta-phi)))
                 +16*(t**10*R**2*k**3*(3*sp.cos(theta)+sp.cos(2*phi-theta))
                      +t**11*R**sp.Rational(3, 2)*k**4
                      *(3*sp.cos(psi)+sp.cos(3*theta-phi)))+t**8)
    involution = {t: -t, theta: -theta, phi: sp.pi-phi}
    for expression in (norm, objective):
        transformed = expression.subs(involution, simultaneous=True)
        assert sp.simplify(sp.expand_trig(transformed-expression)) == 0

    return {
        "all_exact_checks_passed": True,
        "q_definition": "2^(-3/4)",
        "X_through_z4": str(X),
        "fixed_phase_H0_H2_H4_H6": [str(v) for v in
                                   (H0_fixed, H2_fixed, H4_fixed, H6_fixed)],
        "hessian_H0": str(hessian),
        "coordinate_shift_t2": [str(v) for v in y2],
        "coordinate_shift_t3": [str(v) for v in y3],
        "K8": str(K8),
        "K10_before_q_substitution": str(K10),
        "K10": "869/(216*2^(3/4))",
        "K12_fixed": str(fixed_twelfth),
        "K12_amplitude_adjustment": str(amplitude_twelfth),
        "K12_phase_adjustment": str(phase_twelfth),
        "K12_before_q_substitution": str(K12),
        "K12": "65759/(5832*2^(3/2))",
        "signed_t_involution_verified": True,
    }


def numerical_stationary_branch():
    import mpmath as mp
    mp.mp.dps = 80
    q = mp.power(2, -mp.mpf(3)/4)
    c4 = 6*mp.sqrt(2)
    c6 = mp.power(2, mp.mpf(3)/4)/3
    c8 = mp.mpf(20)/9
    c10 = 869*q/216
    c12 = mp.mpf(65759)/(5832*mp.power(2, mp.mpf(3)/2))
    phase_leading = 19*q**mp.mpf("1.5")/27
    records = []
    errors = []
    for t in map(mp.mpf, ("0.03", "0.01", "0.003")):
        def norm(R, k, theta, phi):
            return (8*R**4+16*(1+mp.cos(phi)**2)*R**3*k**2*t**2
                    +48*R**2*k**4*t**4
                    +16*(1+mp.cos(2*theta-phi)**2)*R*k**6*t**6
                    +8*k**8*t**8-1)

        def objective(R, k, theta, phi):
            psi = phi-theta
            return (1+24*(t**4*R**2+t**8*k**4)
                    +16*(t**6*R**2*k*mp.cos(theta)
                         +t**9*mp.sqrt(R)*k**4*mp.cos(psi))
                    +24*((3+mp.cos(2*theta))*t**8*R**2*k**2
                         +(3+mp.cos(2*psi))*t**10*R*k**4
                         +2*t**9*R**mp.mpf("1.5")*k**3
                         *(mp.cos(phi)+mp.cos(2*theta-phi)))
                    +16*(t**10*R**2*k**3
                         *(3*mp.cos(theta)+mp.cos(2*phi-theta))
                         +t**11*R**mp.mpf("1.5")*k**4
                         *(3*mp.cos(psi)+mp.cos(3*theta-phi)))+t**8)

        def equations(R, k, theta, phi):
            point = (R, k, theta, phi)
            norm_R = mp.diff(norm, point, (1, 0, 0, 0))
            objective_R = mp.diff(objective, point, (1, 0, 0, 0))
            result = [norm(*point)]
            for index in range(1, 4):
                derivative = tuple(int(j == index) for j in range(4))
                result.append((mp.diff(objective, point, derivative)
                               -objective_R/norm_R
                               *mp.diff(norm, point, derivative))/t**6)
            return tuple(result)

        starting = (q, q/3+31*q**2*t**2/27,
                    phase_leading*t**3, mp.pi/2-phase_leading*t**3)
        solution = mp.findroot(equations, starting, tol=mp.mpf("1e-65"))
        residual_equations = max(abs(v) for v in equations(*solution))
        assert residual_equations < mp.mpf("1e-60")
        value = objective(*solution)
        residual = (value-1-c4*t**4-c6*t**6-c8*t**8-c10*t**10)/t**12
        errors.append(abs(residual-c12))
        records.append({
            "t": str(t),
            "twelfth_residual": mp.nstr(residual, 35),
            "target_K12": mp.nstr(c12, 35),
            "error_divided_by_t_squared": mp.nstr((residual-c12)/t**2, 30),
            "theta_divided_by_t_cubed": mp.nstr(solution[2]/t**3, 30),
            "pi_half_minus_phi_divided_by_t_cubed":
                mp.nstr((mp.pi/2-solution[3])/t**3, 30),
            "target_phase_coefficient": mp.nstr(phase_leading, 30),
            "stationarity_residual": mp.nstr(residual_equations, 8),
        })
    assert all(errors[j+1] < errors[j] for j in range(len(errors)-1))
    return {
        "precision_decimal_digits": mp.mp.dps,
        "scope": "Stationary branch only; no numerical global-optimality claim.",
        "records": records,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-numerics", action="store_true")
    args = parser.parse_args()
    report = {"symbolic": symbolic_checks()}
    if not args.skip_numerics:
        report["numerical"] = numerical_stationary_branch()
    destination = Path(__file__).resolve().parents[1]/"data"/"twelfth_order_checks.json"
    destination.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"all_exact_checks_passed": True,
                      "numerical_branch_checked": not args.skip_numerics,
                      "report": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
