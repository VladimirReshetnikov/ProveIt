"""Executable symbolic fixed-order endpoint generator.

For every requested finite K this performs finite t-extraction, retaining
exp(q*z**2) EXACTLY. We conjugate D=z*d/dz by that exponential:
  exp(-q*z**2) D exp(q*z**2) P = z*P' + 2*q*z**2*P.
Thus only polynomials are stored; no Taylor cutoff in z is applied to exp(q*z²).

Public provenance: gamma-ratio/Stirling and falling-factorial expansions.
The endpoint specialization follows the accompanying report. The independent
audit's check_all_orders_independent.py supplied a C2 cross-check; this module
implements the full finite-K operator rather than copying its C2-only check.

hL_J symbols mean h_L^(J)(0)/(J!*h_0(0)); pM means [e^M]psi(e).
q=b*(lambda/a)^2 and s=lambda/a are kept as separate symbols for readability.
All coefficients are formal functions of finitely many such jet inputs.
"""
import argparse
import json
from pathlib import Path
import sympy as sp

z, x, lam, s, q = sp.symbols("z x lambda s q", nonzero=True)


def finite_exp(exponent, order):
    """Coefficients of exp(sum_{j>=1} exponent[j]*t^j) through order."""
    result = [sp.Integer(1)]
    for n in range(1, order+1):
        result.append(sp.expand(sum(j*exponent[j]*result[n-j]
                                    for j in range(1, n+1))/n))
    return result


def power_sum(order, argument=x):
    """Polynomial continuation of sum_{i=0}^{argument-1} i^order."""
    return sp.expand((sp.bernoulli(order+1, argument)-sp.bernoulli(order+1, 0))/(order+1))


def falling_factorial_operators(order):
    exponent = [sp.Integer(0)] + [-power_sum(j)/(j*lam**j) for j in range(1, order+1)]
    return finite_exp(exponent, order)


def conjugated_euler(poly):
    return sp.expand(z*sp.diff(poly, z)+2*q*z*z*poly)


def apply_operator(operator, poly):
    operator = sp.Poly(operator, x)
    derivatives = [poly]
    for _ in range(operator.degree()):
        derivatives.append(conjugated_euler(derivatives[-1]))
    return sp.expand(sum(coefficient*derivatives[monomial[0]]
                         for monomial, coefficient in operator.terms()))


def generate(order):
    """Return C_0,...,C_order, valid for any fixed nonnegative integer order."""
    if not isinstance(order, int) or order < 0:
        raise ValueError("order must be a nonnegative integer")
    pressure = [sp.Integer(0)] + [sp.Symbol(f"p{j+2}")*s**(j+2)*z**(j+2)
                                for j in range(1, order+1)]
    pressure_exp = finite_exp(pressure, order)
    amplitude = []
    for n in range(order+1):
        value = sp.Integer(0)
        for ell in range(n//2+1):
            j = n-2*ell
            h = sp.Integer(1) if (ell, j) == (0, 0) else sp.Symbol(f"h{ell}_{j}")
            value += h*s**j*z**j
        amplitude.append(value)
    # F = exp(q*z²) * sum f[n]*t^n.
    f = [sp.expand(sum(amplitude[j]*pressure_exp[n-j] for j in range(n+1)))
         for n in range(order+1)]
    operators = falling_factorial_operators(order)
    return [sp.factor(sum(apply_operator(operators[j], f[n-j]).subs(z, 1)
                          for j in range(n+1))) for n in range(order+1)]


def gamma_ratio_coefficients(order, alpha=None):
    """Q_j(alpha): Gamma(n-alpha)/Gamma(n+1) ~ n^(-alpha-1) sum Q_j/n^j."""
    if alpha is None:
        alpha = sp.Symbol("alpha")
    exponent = [sp.Integer(0)] + [
        (-1)**(r+1)*(sp.bernoulli(r+1, -alpha)-sp.bernoulli(r+1, 1))/(r*(r+1))
        for r in range(1, order+1)]
    return finite_exp(exponent, order)


def inner_transfer(order):
    """h_ell from positive-branch Puiseux coefficients c_{2m+1}."""
    return [sp.simplify(sum(sp.Symbol(f"c{2*m+1}") *
                           gamma_ratio_coefficients(ell-m, sp.Rational(2*m+1, 2))[ell-m] /
                           sp.gamma(-sp.Rational(2*m+1, 2)) for m in range(ell+1)))
            for ell in range(order+1)]


def puiseux_coefficients(phi, w, y, radius, height, count):
    """Generic symbolic inner-jet builder for y=phi(w,y).

    phi may contain additional analytic parameters. The caller supplies a
    characteristic solution height=phi(radius,height), phi_y=1. Analytic
    nested inputs must be substituted into phi to the desired finite order.
    This helper constructs c1,...,c_count in powers of X=sqrt(1-w/radius),
    selecting the negative square-root branch. Singular/nonanalytic inputs
    are rejected rather than silently discarding Puiseux terms.
    """
    if count < 1:
        return []
    at = {w: radius, y: height}
    c1 = -sp.sqrt(2*radius*sp.diff(phi, w).subs(at)/sp.diff(phi, y, 2).subs(at))
    coefficients = [sp.simplify(c1)]
    X = sp.Symbol("X")
    for j in range(2, count+1):
        unknown = sp.Symbol(f"inner_c{j}")
        yy = height+sum(c*X**k for k, c in enumerate(coefficients, 1))+unknown*X**j
        residual = sp.series(phi.subs({w: radius*(1-X*X), y: yy}, simultaneous=True)-yy,
                             X, 0, j+2).removeO().expand().coeff(X, j+1)
        linear = sp.diff(residual, unknown)
        assert sp.simplify(sp.diff(linear, unknown)) == 0
        if sp.simplify(linear) == 0:
            raise ValueError("Degenerate critical germ")
        coefficients.append(sp.simplify(-residual.subs(unknown, 0)/linear))
    return coefficients


def verify_symbolics():
    coefficients = generate(3)
    alpha1, alpha2, kappa, u, v = sp.symbols("alpha1 alpha2 kappa u v")
    substitution = {sp.Symbol("h0_1"): alpha1, sp.Symbol("h0_2"): alpha2,
                    sp.Symbol("h1_0"): kappa, sp.Symbol("p3"): u/s**3,
                    sp.Symbol("p4"): v/s**4}
    C1 = alpha1*s+u-(2*q*q+q)/lam
    C2 = kappa+alpha2*s*s+v+alpha1*s*u+u*u/2 \
        -(alpha1*s*(4*q*q+6*q)+u*(4*q*q+14*q+6))/(2*lam) \
        +(2*q**4+sp.Rational(26, 3)*q**3+sp.Rational(11, 2)*q*q)/lam**2
    assert coefficients[0] == 1
    residual1 = sp.simplify(coefficients[1].subs(substitution)-C1)
    residual2 = sp.simplify(coefficients[2].subs(substitution)-C2)
    assert residual1 == residual2 == 0
    a, b, c, p4 = sp.symbols("a b c p4", nonzero=True)
    beta = b/a**2
    A = alpha1/a-beta
    B = c/a**3-2*beta**2
    C22 = alpha2/a**2-3*alpha1*beta/a-3*c/a**3+sp.Rational(11, 2)*beta**2
    C24 = p4/a**4+alpha1*c/a**4-2*alpha1*beta**2/a-7*c*beta/a**3+sp.Rational(26, 3)*beta**3
    specialize = {s: lam/a, q: beta*lam**2, u: c*lam**3/a**3, v: p4*lam**4/a**4}
    compact1 = sp.simplify(C1.subs(specialize)-(A*lam+B*lam**3))
    compact2 = sp.simplify(C2.subs(specialize)-(kappa+C22*lam**2+C24*lam**4+B*B*lam**6/2))
    assert compact1 == compact2 == 0
    operators = falling_factorial_operators(4)
    t = sp.Symbol("t")
    for degree in range(10):
        exact = sp.Poly(sp.prod(1-i*t/lam for i in range(degree)), t)
        for j in range(5):
            assert sp.simplify(operators[j].subs(x, degree)-exact.nth(j)) == 0
    assert gamma_ratio_coefficients(2, sp.Rational(1, 2)) == [1, sp.Rational(3, 8), sp.Rational(25, 128)]
    w, y = sp.symbols("w y")
    # Solvable square-root model: y=w+y²/2 has r=1/2,tau=1,
    # y=1-sqrt(1-2w), so the chosen c1=-1 and all later c_j=0.
    assert puiseux_coefficients(w+y*y/2, w, y, sp.Rational(1, 2), 1, 4) == [-1, 0, 0, 0]
    return {"C0": "1", "C1_residual": str(residual1), "C2_residual": str(residual2),
            "C1_compact_polynomial_residual": str(compact1),
            "C2_compact_polynomial_residual": str(compact2),
            "falling_factorial_tests": "orders 0..4; monomials z^j, j=0..9",
            "gamma_ratio_check": "Q0(1/2)=1, Q1(1/2)=3/8, Q2(1/2)=25/128",
            "generic_Puiseux_check": "four coefficients of y=w+y^2/2",
            "untruncated_gaussian": "exact conjugated Euler operator; no z-series cutoff",
            "generated_through_order": 3,
            "coefficients": [str(c) for c in coefficients],
            "inner_transfer_through_2": [str(c) for c in inner_transfer(2)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=2)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify_symbolics() if args.verify else {
        "order": args.order, "coefficients": [str(c) for c in generate(args.order)],
        "inner_transfer": [str(c) for c in inner_transfer(args.order//2)]}
    output = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
