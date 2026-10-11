"""Exact coefficient and formal-kernel checks for the Tornheim cubic theorem.

This verifies algebra used in the proof. It does not assert numerical or
arithmetic independence of the two retained constants.
"""
import json
from pathlib import Path

import sympy as s


def main():
    t, A, B, C = s.symbols("t A B C")
    a, b, c = s.symbols("a b c")
    g, z2, z3 = s.symbols("gamma zeta2 zeta3")
    z10, z20, z30, zm1, zm2, zm3 = s.symbols(
        "zeta_prime_0 zeta_second_0 zeta_third_0 "
        "zeta_prime_minus1 zeta_second_minus1 zeta_third_minus1"
    )
    U, V = s.symbols("J_AA J_AB")

    def trunc(expr, degree=3):
        return s.series(expr, t, 0, degree + 1).removeO().expand()

    def series_gamma_ratio(x, y):
        log_series = (g * (x + y) * t + z2 * (x*x-y*y) * t*t / 2
                      + z3 * (x**3+y**3) * t**3 / 3)
        return trunc(sum(log_series**j / s.factorial(j) for j in range(4)))

    def series_zeta_zero(x):
        return -s.Rational(1, 2) + z10*x*t + z20*x*x*t*t/2 + z30*x**3*t**3/6

    def series_zeta_minus1(x):
        return -s.Rational(1, 12) + zm1*x*t + zm2*x*x*t*t/2 + zm3*x**3*t**3/6

    # Derive the elementary third derivative by direct formal multiplication.
    elementary = series_zeta_zero(a) * series_zeta_zero(b)
    elementary -= c/(a+c) * series_gamma_ratio(a, c) * series_zeta_minus1(b)
    elementary -= c/(b+c) * series_gamma_ratio(b, c) * series_zeta_minus1(a)
    elementary_third = 6 * s.expand(elementary).coeff(t, 3)

    # Independently extract M=J_AA+2J_AC from the symmetric polar term.
    gpA = 1 + g*A + (g*g+z2)*A*A/2 + (g**3+3*g*z2+2*z3)*A**3/6
    gpC = gpA.xreplace({A:C})
    reciprocalA = 1 + g*A + (g*g-z2)*A*A/2 + (g**3-3*g*z2+2*z3)*A**3/6
    reciprocalC = reciprocalA.xreplace({A:C})
    zmA = -s.Rational(1,12) + zm1*A + zm2*A*A/2 + zm3*A**3/6
    zmC = zmA.xreplace({A:C})
    trig = 1-z2*(A*A-A*C+C*C)
    polar_pair = gpA*gpC*trig/12-zmA*reciprocalC-zmC*reciprocalA
    polar_AAC = s.expand(polar_pair).coeff(A, 2).coeff(C, 1)
    M = s.expand(z10*z20-z30-2*polar_AAC)
    M_expected = z10*z20-z30+g*zm2+(g*g-z2)*zm1-(g**3+g*z2)/12
    assert s.expand(M-M_expected) == 0

    axis_numerator = (series_zeta_minus1(1) - series_zeta_zero(1)
                      - series_gamma_ratio(0, 1)/6 - s.Rational(1, 4))
    Y = 2*s.expand(axis_numerator).coeff(t, 3)
    Y_expected = (zm3-z30)/3-(g**3-3*g*z2+2*z3)/18
    assert s.expand(Y-Y_expected) == 0

    phi = c*(a*a+b*b-c*(a+b))
    third_raw = (elementary_third+3*phi*U+6*a*b*c*V
                 +3*c*c*(a+b)*M+3*c**3*Y)
    kappa = 3*U+g**3/12+g*z2/4+z3/6-3*g*zm2
    omega = 6*V-6*(g*g+z2)*zm1+12*z10*z20-8*z30
    Q = (3*(a+b)*(a*b+c*c)*z10*z20
         -((a**3+b**3)/2+3*c*c*(a+b)+c**3)*z30
         +(c**3-c*(a**3/(b+c)+b**3/(a+c)))*zm3)
    third_theorem = a*b*c*(omega-12*z10*z20+8*z30)+phi*kappa+Q
    assert s.cancel(third_raw-third_theorem) == 0

    rays = [(1,1,2,3),(4,2,3,1),(-5,3,1,2)]
    assert sum(w*aa*bb*cc for w,aa,bb,cc in rays) == 0
    assert sum(w*phi.subs({a:aa,b:bb,c:cc}) for w,aa,bb,cc in rays) == 0
    combo = s.expand(sum(w*third_raw.subs({a:aa,b:bb,c:cc})
                         for w,aa,bb,cc in rays))
    target = 99*z10*z20+s.Rational(207,2)*z30+s.Rational(162,5)*zm3
    assert s.expand(combo-target) == 0
    two_ray = third_raw.subs({a:3,b:6,c:5})-90*third_raw.subs({a:1,b:1,c:1})
    two_ray_target = 81*z10*z20-s.Rational(403,2)*z30-s.Rational(245,11)*zm3
    assert s.expand(two_ray-two_ray_target) == 0

    # Build the restriction matrix directly in each homogeneous polynomial space.
    rank_rows = []
    for d in range(1, 11):
        n = d-1
        basis = []
        for i in range(n+1):
            for j in range(i,n+1):
                k = n-i-j
                if k < 0:
                    continue
                monomial = A**i*B**j*C**k
                if i != j:
                    monomial += A**j*B**i*C**k
                basis.append(monomial)
        constraint_cols = []
        for h in basis:
            q = h.subs(B,0)
            condition = s.expand(C*q+A*q.xreplace({A:C,C:A}))
            constraint_cols.append([condition.coeff(A,j).coeff(C,d-j)
                                    for j in range(d+1)])
        mat = s.Matrix(d+1, len(basis),
                       lambda i,j:constraint_cols[j][i])
        dim = len(basis)-mat.rank()
        expected = 0 if d<3 else (d*d-1)//4
        assert dim == expected
        diagonal = s.Matrix([[h.subs({A:1,B:1,C:1}) for h in basis]])
        fixed_diagonal_dim = len(basis)-mat.col_join(diagonal).rank()
        assert fixed_diagonal_dim == max(expected-1,0)
        rank_rows.append({"degree":d,"ambient_dimension":len(basis),
                          "constraint_rank":mat.rank(),"kernel_dimension":dim,
                          "fixed_diagonal_dimension":fixed_diagonal_dim})

    output = {"status":"PASS", "method":"Exact SymPy polynomial and rational identities",
              "checks":["M extracted from symmetric polar part",
                        "J_CC extracted from axis",
                        "complete cubic formula",
                        "three-ray cancellation",
                        "two-ray cancellation on Phi=0",
                        "formal ambiguity dimensions through degree 10"],
              "three_ray_coefficients":{"zeta_prime_0_times_second_0":"99",
                                        "zeta_third_0":"207/2",
                                        "zeta_third_minus1":"162/5"},
              "kernel_dimensions":rank_rows}
    destination = Path(__file__).resolve().parent.parent / "results" / "tornheim_cubic_symbolic.json"
    destination.write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
