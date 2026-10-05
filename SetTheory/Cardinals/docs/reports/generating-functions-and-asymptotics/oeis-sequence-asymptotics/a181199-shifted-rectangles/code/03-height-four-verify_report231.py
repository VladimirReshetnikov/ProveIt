#!/usr/bin/env python3
"""Replay the height-four proof certificate using Python's standard library.

Run: python -B verify_report231.py
The default output is deterministic JSON. --receipt PATH creates a NEW file;
it never replaces an existing file. --self-test additionally exercises rejection
of corrupted identities. All guards raise exceptions and survive python -O.

Symbolic identities constitute the algebra certificate. Finite counting tests
are independent consistency checks, not a substitute for the manuscript's proof.
"""
import argparse
from fractions import Fraction as F
import json
from math import comb, factorial as fac
from pathlib import Path
import sys

from exact_algebra import N, U, V, Poly, Rat, require, self_test as algebra_self_test
from formal_series import asymptotic_data, div as series_div, series


def polynomial_zero(residual, name):
    require(isinstance(residual, Poly) and not residual,
            "nonzero polynomial certificate residual: " + name)


def rational_zero(residual, name):
    require(isinstance(residual, Rat) and not residual.num,
            "nonzero rational certificate residual after denominator clearing: " + name)


def symbolic_checks():
    algebra_self_test()
    checks = []
    def pcheck(name, residual):
        polynomial_zero(residual, name)
        checks.append({"name": name, "ring": "Q[n,u,v]", "residual": "0"})
    def rcheck(name, residual):
        rational_zero(residual, name)
        checks.append({"name": name, "ring": "Q[n] after rational-denominator clearing",
                       "residual": "0"})
    n, u, v = N, U, V
    f = u*v*(u+v-1)
    # L clears every denominator in P and Q. Its zeros n=0,-1 are excluded.
    L = n**2*(n+1)**2
    p21 = (n+3)*(3*n+1)*(3*n+2)
    p20 = -(3*n+1)*n*(n+1)
    p12 = 3*(3*n+1)*(3*n+2)*(n+1)
    p11 = -(3*n+1)*(7*n**2+14*n+6)
    p10 = (n-1)*n*(n+1)
    p00 = n*(n+1)**2
    P = u*v*(p21*u**2*v+p20*u**2+p12*u*v**2+p11*u*v+p10*u+p00)
    Q = P.substitute({1: v, 2: u})
    atilde_top = 3*(3*n+1)*(3*n+2)
    pcheck("divergence identity with Pbar=L*P and Qbar=L*Q",
           f*(P.derivative(1)+Q.derivative(2))
           +(n-1)*(P*f.derivative(1)+Q*f.derivative(2))
           -f*(atilde_top*(n+1)**2*f+L)*(u+v))
    pcheck("lower edge stronger factorization",
           P+Q-f*((p21+p12)*u*v+p20*(u+v)-2*n*(n+1)**2))
    pcheck("lower edge u+v=1 including n=1", (P+Q).substitute({2: 1-u}))
    pcheck("vertical edge u=1",
           P.substitute({1: 1})-(p12*v**3-n*(3*n+1)*(4*n+3)*v**2-n*(n+1)**2*v))
    pcheck("horizontal edge v=1",
           Q.substitute({2: 1})-(p12*u**3-n*(3*n+1)*(4*n+3)*u**2-n*(n+1)**2*u))
    pcheck("n=1 nonsingular divergence identity",
           (P.derivative(1)+Q.derivative(2)).substitute({0: 1})
           -4*(60*f+1)*(u+v))
    pcheck("n=1 lower edge without a vanishing power of f",
           (P+Q).substitute({0: 1, 2: 1-u}))
    # Integrate each monomial v^(2n-2+j), not just a pre-simplified flux formula.
    def integrate_upper_edge(edge, variable):
        result = Rat()
        for exponent, coefficient in edge.terms.items():
            other = 2 if variable == 1 else 1
            require(exponent[other] == 0, "unexpected upper-edge variable")
            result += Rat(coefficient*n**exponent[0], L*(2*n-1+exponent[variable]))
        return result
    vertical = integrate_upper_edge(P.substitute({1: 1}), 2)
    horizontal = integrate_upper_edge(Q.substitute({2: 1}), 1)
    num = 28*n**3+50*n**2+29*n+5
    total_flux = Rat(num, n**2*(n+1)**2*(2*n+1))
    rcheck("vertical boundary integral", vertical-total_flux/2)
    rcheck("horizontal boundary integral", horizontal-total_flux/2)
    rcheck("sum of all three outward boundary fluxes", vertical+horizontal-total_flux)
    # Integrated divergence: multiply by n^2(n+1)^2/2 to recover the Z recurrence.
    rcheck("triangle recurrence coefficient Z_(n+1)",
           Rat(atilde_top, n**2)*Rat(2, (n+1)**2)*Rat(L, 2)-Rat(atilde_top))
    rcheck("triangle recurrence coefficient Z_n", Rat(2, n**2)*Rat(L, 2)-Rat((n+1)**2))
    rcheck("triangle recurrence right side", total_flux*Rat(L, 2)-Rat(num, 2*(2*n+1)))

    alpha = Rat(4*(n-1), 4*n-1)
    offset = Rat(-(32*n**3-56*n**2+28*n-5), 8*(2*n-1)**2*(4*n-1))
    # The normalized trace reduction is affine in Z=N^3 H.
    rcheck("trace reduction coefficient of Z", Rat(-12*n, 4*n-1)+4-alpha)
    rcheck("trace reduction constant",
           Rat(1, 8*(2*n-1)**2)+Rat(2*n, 4*n-1)-F(3, 4)-offset)
    mr = Rat(8*(2*n+1)*(4*n+1)*(4*n+3), (n+1)**3)
    factorial_mr = Rat((4*n+1)*(4*n+2)*(4*n+3)*(4*n+4), (n+1)**4)
    rcheck("multinomial factorial ratio", mr-factorial_mr)
    A = Rat(3*(n-1)*(n+1)*(3*n+1)*(3*n+2))
    B = Rat(8*n*(2*n+1)*(4*n-1)*(4*n+1))
    D = Rat(6*(4*n+1)*(7*n**2-1), (n+1)**2*(2*n-1)**2*(2*n+1))
    znext_coefficient = Rat(-(n+1)**2, atilde_top)
    znext_constant = Rat(num, 2*(2*n+1)*atilde_top)
    rcheck("affine substitution coefficient of Z_n",
           A*mr*alpha.shift()*znext_coefficient+B*alpha)
    rcheck("affine substitution constant",
           A*mr*(alpha.shift()*znext_constant+offset.shift())+B*offset-D)
    rcheck("normalization multiplier R_n",
           -B/(A*mr)-Rat(-n*(n+1)**2*(4*n-1),
                        3*(n-1)*(3*n+1)*(3*n+2)*(4*n+3)))
    rcheck("normalization forcing S_n",
           D/(A*mr)-Rat(7*n**2-1,
                       4*(n-1)*(3*n+1)*(3*n+2)*(2*n-1)**2*(2*n+1)**2*(4*n+3)))
    q = Rat(8*(2*n-1)**2*(4*n+3)*(4*n+5)*(7*n**2+14*n+6),
            (n+1)*(n+2)**2*(2*n+3)*(7*n**2-1))
    rcheck("hypergeometric forcing ratio q_n", D.shift()/D*mr-q)
    p0 = -64*(2*n-1)**2*(2*n+1)*(4*n-1)*(4*n+1)*(4*n+3)*(4*n+5)*(7*n**2+14*n+6)
    p1 = -8*(n+1)*(2*n+1)*(4*n+3)*(4*n+5)*(364*n**5+84*n**4-1025*n**3-534*n**2+157*n+54)
    p2 = 3*(n+1)*(2*n+3)*(3*n+4)*(3*n+5)*(7*n**2-1)*(n+2)**3
    scale = Rat((n+1)*(n+2)**2*(2*n+3)*(7*n**2-1), n)
    rcheck("OEIS elimination coefficient p0", Rat(p0)+scale*q*B)
    rcheck("OEIS elimination coefficient p1", Rat(p1)-scale*(B.shift()-q*A))
    rcheck("OEIS elimination coefficient p2", Rat(p2)-scale*A.shift())
    n0 = sum(p.value(n=0) for p in (p0, p1, p2))
    require(n0 == -2160, "incorrect explicit n=0 residual")
    require(A.value(1) == 0 and B.value(1) == 360 and D.value(1)*24 == 360,
            "first-order recurrence n=1 check failed")
    require(alpha.value(1)*F(1, 3)+offset.value(1) == F(1, 24),
            "full-count affine formula n=1 check failed")

    # Exact finite-sum correspondence: factorial ratios and initial values.
    product4 = (4*n-1)*(4*n)*(4*n+1)*(4*n+2)
    product3 = (3*n+1)*(3*n+2)*(3*n+3)
    fratio = Rat(-product4, (n-1)*product3)
    rcheck("finite-sum prefactor homogeneous ratio", fratio+B/A)
    fnext_t_over_m = Rat(3*(7*n**2-1)*(n+1)*n*(4*n+1)*(4*n+2),
                        product3*(n+1)*(n-1)*n*(n+1)**2*(2*n-1)**2*(2*n+1)**2)
    rcheck("finite-sum summand variation of constants", A*fnext_t_over_m-D)
    printed_prefactor_ratio = Rat(-64*n, n-1)*Rat(2*n-F(1, 2))*Rat(2*n+F(1, 2))*Rat(n+F(1, 2))/Rat(product3)
    rcheck("printed Conjecture 18 prefactor ratio", printed_prefactor_ratio-fratio)
    rcheck("rising factorial (-1/2)_(2n) factorial identity ratio",
           Rat(product4, 16*(2*n)*(2*n+1))-Rat((2*n-F(1, 2))*(2*n+F(1, 2))))
    rcheck("rising factorial (1/2)_n factorial identity ratio",
           Rat((2*n+1)*(2*n+2), 4*(n+1))-Rat(n+F(1, 2)))
    rcheck("half-integer binomial factorial identity ratio",
           Rat((2*n+3)*(2*n+2), 4*(n+1)**2)-Rat(n+F(3, 2), n+1))
    den_t = (n-1)*n*(n+1)**2*(2*n-1)**2*(2*n+1)**2
    den_printed = den_t*(2*n+1)
    common = Rat(7*(n+1)**2-1, 7*n**2-1)
    t_ratio = -common*Rat(product3, (n+1)**3)*Rat(den_t)/Rat(den_t).shift()
    printed_t_ratio = -4*common*Rat(product3, (2*n+1)*(2*n+2)*(n+1))*Rat((2*n+3)*(2*n+2), 4*(n+1)**2)*Rat(den_printed)/Rat(den_printed).shift()
    rcheck("printed Conjecture 18 summand ratio", printed_t_ratio-t_ratio)
    return checks, {"A": A, "B": B, "D": D, "alpha": alpha, "offset": offset,
                    "R": -B/(A*mr), "S": D/(A*mr),
                    "p0": p0, "p1": p1, "p2": p2}, str(n0)


def z_signed_h(n):
    """Integrate the independently expanded polynomial h(t)."""
    return fac(n)**2*sum((F((-1)**j, fac(n-1-j)*fac(n+j)*(2*n+j+1))
                         for j in range(n)), F(0))


def z_direct_triangle(n):
    """Positive barycentric/Dirichlet integration, with no recurrence used.

    x=1-u, y=1-v, z=u+v-1, x+y+z=1. Then
    Z=n^2 integral (y+z)^n(x+z)^(n-1)z^(n-1) dx dy.
    Integrate every expanded monomial by i!j!k!/(i+j+k+2)!.
    """
    numerator = 0
    for i in range(n+1):
        for j in range(n):
            k = 3*n-2-i-j
            require(k >= 0, "negative Dirichlet exponent")
            numerator += comb(n, i)*comb(n-1, j)*fac(i)*fac(j)*fac(k)
    return F(n*n*numerator, fac(3*n))


def prefix_dp(n):
    """Independent legal-prefix count from literal cell predecessors.

    A prefix length x[r] records filled cells in row r. To append column c to
    row r>0, the preceding row must contain columns c and min(c+1,n-1).
    These are the vertical and downward-antidiagonal predecessors; the other
    adjacent prerequisites are already enforced by prefix order.
    """
    require(n >= 1, "positive width required")
    layer = {(0, 0, 0, 0): 1}
    visited = 1
    for _ in range(4*n):
        next_layer = {}
        for state, count in layer.items():
            for row in range(4):
                column = state[row]
                if column == n:
                    continue
                if row and state[row-1] < min(column+2, n):
                    continue
                new_state = state[:row]+(column+1,)+state[row+1:]
                next_layer[new_state] = next_layer.get(new_state, 0)+count
        layer = next_layer
        visited += len(layer)
    require(set(layer) == {(n, n, n, n)}, "prefix DP did not end at the full array")
    return layer[(n, n, n, n)], visited


def rising(x, count):
    result = F(1)
    for i in range(count):
        result *= x+i
    return result


def finite_prefactor(n):
    return F((-1)**(n+1)*n*(n-1)*fac(4*n-2), fac(n)*fac(3*n))


def finite_term(n):
    return F(3*(-1)**n*(7*n*n-1)*fac(3*n),
             fac(n)**3*(n-1)*n*(n+1)**2*(2*n-1)**2*(2*n+1)**2)


def printed_prefactor(n):
    return F((-64)**n*(n-1), 4*fac(3*n))*rising(F(-1, 2), 2*n)*rising(F(1, 2), n)


def printed_term(n):
    half_binomial = rising(F(3, 2), n)/fac(n)
    return F((-4)**n*(7*n*n-1)*comb(3*n, 2*n),
             (n-1)*n*(n+1)**2*(2*n-1)**2*(2*n+1)**3)*half_binomial


def finite_checks(data, maximum=20):
    require(maximum == 20, "the archival certificate requires exactly widths 1 through 20")
    zs = {n: z_direct_triangle(n) for n in range(1, maximum+2)}
    require(zs[1] == F(1, 3), "Z_1 is incorrect")
    require(rising(F(-1, 2), 2) == -F(1, 4), "first rising-factorial base failed")
    require(rising(F(1, 2), 0) == 1 and rising(F(3, 2), 0) == 1,
            "remaining factorial identity bases failed")
    require(finite_prefactor(2) == -1 and printed_prefactor(2) == -1,
            "Conjecture 18 prefactor initial value failed")
    require(3*printed_term(2) == finite_term(2), "Conjecture 18 summand initial value failed")
    counts, records = {}, []
    finite_sum = -F(1)
    for n in range(1, maximum+1):
        require(z_signed_h(n) == zs[n], "signed and positive triangle integrals differ")
        multinomial = F(fac(4*n), fac(n)**4)
        direct_count = multinomial*(data["alpha"].value(n)*zs[n]+data["offset"].value(n))
        dp_count, visited = prefix_dp(n)
        require(direct_count.denominator == 1 and direct_count == dp_count,
                "direct triangle integral / independent DP mismatch at n="+str(n))
        require(3*(3*n+1)*(3*n+2)*zs[n+1]+(n+1)**2*zs[n]
                == F(28*n**3+50*n*n+29*n+5, 2*(2*n+1)),
                "triangle recurrence finite check failed")
        if n >= 2:
            require(printed_prefactor(n) == finite_prefactor(n),
                    "printed finite-sum prefactor mismatch")
            require(3*printed_term(n) == finite_term(n), "printed finite-sum term mismatch")
            require(finite_prefactor(n)*finite_sum == dp_count, "finite-sum count mismatch")
            finite_sum += finite_term(n)
        counts[n] = dp_count
        records.append({"n": n, "count_prefix_dp": dp_count,
                        "count_direct_triangle": int(direct_count),
                        "Z_positive_dirichlet": str(zs[n]),
                        "Z_signed_h": str(z_signed_h(n)),
                        "prefix_states_visited": visited})
    require(counts[1] == counts[2] == 1, "initial counts are incorrect")
    for n in range(1, maximum):
        require(data["A"].value(n)*counts[n+1]+data["B"].value(n)*counts[n]
                == data["D"].value(n)*F(fac(4*n), fac(n)**4),
                "inhomogeneous recurrence finite check failed")
    for n in range(1, maximum-1):
        require(sum(data["p"+str(j)].value(n=n)*counts[n+j] for j in range(3)) == 0,
                "order-two recurrence finite check failed")
    return records


def guard_self_test():
    """A changed coefficient must be rejected even with optimization enabled."""
    caught = []
    for name, action in [
        ("nonzero polynomial", lambda: polynomial_zero(N+U*V, "intentional corruption")),
        ("nonzero rational", lambda: rational_zero(Rat(1, N+1), "intentional corruption")),
        ("zero denominator", lambda: Rat(1, 0)),
        ("pole evaluation", lambda: Rat(1, N-1).value(1)),
        ("false guard", lambda: require(False, "intentional false condition")),
    ]:
        try:
            action()
        except ArithmeticError:
            caught.append(name)
        else:
            raise ArithmeticError("self-test failed to reject " + name)
    return caught


def rational_series_at_infinity(rational, length):
    """Reverse the checked n-polynomials to independently expand at x=1/n."""
    numerator_degree = rational.num.degree()
    denominator_degree = rational.den.degree()
    shift = denominator_degree-numerator_degree
    require(shift >= 0, "this series check does not allow poles at infinity")
    numerator = [F(0)]*shift+[rational.num.coefficient(j)
                             for j in range(numerator_degree, -1, -1)]
    denominator = [rational.den.coefficient(j)
                   for j in range(denominator_degree, -1, -1)]
    return series_div(series(numerator, length), series(denominator, length))


def verify():
    checks, data, n0 = symbolic_checks()
    counts = finite_checks(data)
    series_data = asymptotic_data(12)
    for name in ("R", "S"):
        require([str(x) for x in rational_series_at_infinity(data[name], 13)]
                == series_data[name+"_series_coefficients"],
                "normalized recurrence and formal series input differ: "+name)
    series_data["normalized_rational_input_crosscheck"] = "exact polynomial reversal agrees through x^12"
    return {
        "schema": "report231-exact-certificate-v1",
        "arithmetic": "Python standard library; Fraction; custom sparse polynomials and rational functions",
        "status": "all checks passed",
        "symbolic_check_count": len(checks),
        "symbolic_checks": checks,
        "denominator_scope": {
            "divergence": "n>=1; common denominator n^2(n+1)^2 is nonzero",
            "boundary_integrals": "n>=1; monomial exponents nonnegative; denominators 2n+j-1 positive for j>=1",
            "affine_to_first_order": "n>=2; n=1 checked separately",
            "OEIS_elimination": "n>=1; all displayed denominators nonzero",
            "finite_sum": "n>=2; initial value n=2 and exact shift identities",
            "normalized_recurrence": "n>=2"
        },
        "index_zero": {"optional_counts": [1, 1, 1], "residual": n0,
                       "conclusion": "The order-two operator is not asserted at n=0."},
        "independent_finite_checks": counts,
        "finite_check_scope": "Counts 1..20; triangle identity 1..20; first-order 1..19; order-two 1..18. Consistency tests only.",
        "asymptotics": series_data,
        "guard_self_tests": guard_self_test(),
        "limitations": "The transfer/Pfaffian and analytic remainder arguments are proved in the accompanying manuscript; this program certifies their stated algebraic reductions. No height-five or literature-novelty claim."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="create a new receipt file; never overwrite")
    parser.add_argument("--self-test", action="store_true", help="run explicit guard rejection tests (also always included in the receipt)")
    args = parser.parse_args()
    # Fail before doing work if the requested destination is already occupied.
    if args.receipt is not None:
        destination = args.receipt.absolute()
        if any(path.is_symlink() for path in (destination, *destination.parents)):
            parser.error("receipt destination must not have a symlink ancestor")
        if destination.exists():
            parser.error("receipt destination already exists; choose a fresh path")
    receipt = verify()
    rendered = json.dumps(receipt, indent=2, sort_keys=True)+"\n"
    if args.receipt is not None:
        with args.receipt.open("x", encoding="utf-8", newline="\n") as output:
            output.write(rendered)
    sys.stdout.write(rendered)


if __name__ == "__main__":
    main()
