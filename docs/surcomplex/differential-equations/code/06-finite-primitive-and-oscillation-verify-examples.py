#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

This is NOT an implementation or formal verification of the surreal numbers or
of the Berarducci--Mantova derivation. Ordinary symbolic differentiation checks
finite identities used in the proofs. The Laurent operator D=-t**2*d/dt is an
exact model of the restriction proved in the article.

Requirements: Python 3.10+ and SymPy. No network, random input, or floating point.
Exit status: 0 if every check passes; 1 on failed checks; 2 on missing dependency.
"""
from __future__ import annotations

from collections import Counter
import platform
import sys

try:
    import sympy as sp
except ImportError:
    print("SymPy is required. Install it with: python -m pip install sympy", file=sys.stderr)
    raise SystemExit(2)


class Checks:
    """Collect exact identities and report each named check."""

    def __init__(self) -> None:
        self.results: list[tuple[str, str, bool]] = []

    def zero(self, category: str, name: str, expression: sp.Expr) -> None:
        value = sp.simplify(sp.expand(expression))
        passed = value == 0
        self.results.append((category, name, passed))
        print(f"{'PASS' if passed else 'FAIL'} | {category} | {name}")
        if not passed:
            print(f"  Nonzero residual: {value}")

    def condition(self, category: str, name: str, passed: bool) -> None:
        self.results.append((category, name, bool(passed)))
        print(f"{'PASS' if passed else 'FAIL'} | {category} | {name}")

    def finish(self) -> int:
        counts = Counter(category for category, _, _ in self.results)
        failures = sum(not ok for _, _, ok in self.results)
        print("\nCATEGORY COUNTS")
        for category, count in counts.items():
            print(f"{category}: {count}")
        print(f"\nTOTAL: {len(self.results)} checks; "
              f"{len(self.results) - failures} passed; {failures} failed.")
        print("\nScope: exact finite symbolic identities only. These checks do not prove")
        print("the infinite-support, class-size, or general differential-field theorems.")
        return 1 if failures else 0


def trunc(poly: sp.Expr, variable: sp.Symbol, degree: int) -> sp.Expr:
    """Polynomial truncation through the given degree, without numerical error."""
    p = sp.Poly(sp.expand(poly), variable)
    return sp.Add(*(coeff * variable**power[0]
                    for power, coeff in p.terms() if power[0] <= degree))


def compose_truncated(coefficients: list[sp.Expr], inner: sp.Expr,
                      variable: sp.Symbol, degree: int) -> sp.Expr:
    """Evaluate a finite polynomial modulo variable**(degree+1)."""
    value = sp.S.Zero
    power = sp.S.One
    for coefficient in coefficients:
        value = trunc(value + coefficient * power, variable, degree)
        power = trunc(power * inner, variable, degree)
    return value


def main() -> int:
    print("FINITE SYMBOLIC VERIFICATION")
    print(f"Python: {platform.python_version()}")
    print(f"SymPy: {sp.__version__}")
    print("Arithmetic: exact rational/complex symbolic; deterministic.\n")
    checks = Checks()
    x = sp.Symbol("x", positive=True)
    X, t, z, T = sp.symbols("X t z T")
    I = sp.I

    # Total differentiation after polynomial evaluation.
    for n in range(1, 8):
        F = sum((x**(k + 1) + 1/x) * X**k for k in range(n + 1))
        inner = x*x + 1
        lhs = sp.diff(F.subs(X, inner), x)
        rhs = sp.diff(F, x).subs(X, inner) + sp.diff(F, X).subs(X, inner) * sp.diff(inner, x)
        checks.zero("total chain rule", f"degree {n}", lhs - rhs)

    powers = [sp.Rational(-2), sp.Rational(0), sp.Rational(1, 2),
              sp.Rational(1), sp.Rational(3, 2), sp.Rational(2), sp.Rational(3)]
    for p in powers:
        primitive = sp.log(x) if p == 1 else x**(1-p)/(1-p)
        checks.zero("scale primitives", f"power p={p}", sp.diff(primitive, x)-x**(-p))
    logs = [x]
    for _ in range(3):
        logs.append(sp.log(logs[-1]))
    for m in range(4):
        for p in [sp.Rational(0), sp.Rational(1), sp.Rational(2), sp.Rational(3)]:
            b = 1/(sp.prod(logs[:m]) * logs[m]**p)
            primitive = sp.log(logs[m]) if p == 1 else logs[m]**(1-p)/(1-p)
            checks.zero("scale primitives", f"log depth {m}, p={p}", sp.diff(primitive, x)-b)

    # These are finite truncation identities; Hahn summability is proved in text.
    for n in range(1, 10):
        ec = [sp.S.One/sp.factorial(k) for k in range(n+1)]
        lc = [sp.S.Zero] + [sp.Rational((-1)**(k+1), k) for k in range(1, n+1)]
        E = sum(ec[k]*z**k for k in range(n+1))
        L = sum(lc[k]*z**k for k in range(n+1))
        checks.zero("formal exponential/logarithm", f"exponential derivative n={n}",
                    sp.diff(E, z)-E+z**n/sp.factorial(n))
        checks.zero("formal exponential/logarithm", f"logarithm derivative n={n}",
                    (1+z)*sp.diff(L, z)-1-(-1)**(n+1)*z**n)
        checks.zero("formal exponential/logarithm", f"inverse phases n={n}",
                    trunc(E*E.subs(z, -z)-1, z, n))
        checks.zero("formal exponential/logarithm", f"exp(log) n={n}",
                    compose_truncated(ec, L, z, n)-1-z)
        checks.zero("formal exponential/logarithm", f"log(exp) n={n}",
                    compose_truncated(lc, E-1, z, n)-z)

    # Rational algebra for polar logarithmic derivatives and scalar gauges.
    u, v, du, dv = sp.symbols("u v du dv", real=True)
    rate = (du+I*dv)/(u+I*v)
    coordinate_rate = (u*du+v*dv)/(u*u+v*v)+I*(u*dv-v*du)/(u*u+v*v)
    checks.zero("phase and gauge algebra", "coordinate logarithmic derivative", rate-coordinate_rate)
    for p in [sp.Rational(2), sp.Rational(3), sp.Rational(4)]:
        U = x**4/4
        eta = x**(1-p)/(1-p)
        g = sp.exp(U+I*eta)
        checks.zero("phase and gauge algebra", f"admissible gauge p={p}",
                    sp.diff(g, x)/g - x**3-I*x**(-p))
    P = x**2 + sp.log(x)
    eta = -1/x
    U = x**3/3
    g = sp.exp(U+I*eta)
    q = sp.diff(U, x)+I*sp.diff(P+eta, x)
    checks.zero("phase and gauge algebra", "remove finite phase, retain P prime",
                q-sp.diff(g, x)/g-I*sp.diff(P, x))

    # Differential extension generated by T with T'=iT.
    DT = lambda f: sp.cancel(I*T*sp.diff(f, T))
    c = (T+1/T)/2
    s = (T-1/T)/(2*I)
    cayley = (T-1)/(I*(T+1))
    checks.zero("oscillatory extension", "circle identity", c*c+s*s-1)
    checks.zero("oscillatory extension", "cosine derivative", DT(c)+s)
    checks.zero("oscillatory extension", "sine derivative", DT(s)-c)
    checks.zero("oscillatory extension", "Cayley Riccati derivative", DT(cayley)-(1+cayley*cayley)/2)
    checks.zero("oscillatory extension", "Cayley cosine", c-(1-cayley*cayley)/(1+cayley*cayley))
    checks.zero("oscillatory extension", "Cayley sine", s-2*cayley/(1+cayley*cayley))
    checks.zero("oscillatory extension", "Cayley inverse", T-(1+I*cayley)/(1-I*cayley))
    checks.zero("oscillatory extension", "conjugation fixes real coordinate",
                sp.conjugate(cayley).subs(sp.conjugate(T), 1/T)-cayley)

    # Constant-coefficient modes, checked with x standing for omega.
    root_lists = [[0, 0, 0], [1, -1], [2, 2, I, -I],
                  [-2, -2, 0, 3], [0, 0, 1, I, -I]]
    for j, roots in enumerate(root_lists, 1):
        multiplicities = Counter(roots)
        for lam, multiplicity in multiplicities.items():
            if sp.sympify(lam).is_real:
                for k in range(multiplicity):
                    result = sp.exp(lam*x)*x**k
                    for root in roots:
                        result = sp.expand(sp.diff(result, x)-root*result)
                    checks.zero("constant coefficient modes", f"operator {j}, lambda={lam}, k={k}", result)
    checks.zero("constant coefficient modes", "forced quadratic oscillator",
                sp.diff(x*x-2, x, 2)+(x*x-2)-x*x)
    C0, C1, C2 = sp.symbols("C0 C1 C2")
    N = sp.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    Y = sp.exp(2*x)*(sp.eye(3)+x*N+x*x*N*N/2)*sp.Matrix([C0, C1, C2])
    residual = Y.diff(x)-(2*sp.eye(3)+N)*Y
    for j, entry in enumerate(residual):
        checks.zero("constant coefficient modes", f"Jordan block coordinate {j}", entry)

    D = lambda f: sp.expand(-t*t*sp.diff(f, t))
    # First-order exact residual, three coefficients and two Laurent inputs.
    for a in [I, sp.Integer(2), 1+I]:
        for j, f in enumerate([t, t**(-3)+2*t+t**3], 1):
            term, y = f, sp.S.Zero
            for n in range(1, 11):
                y = sp.expand(y-a**(-n)*term)
                term = D(term)
                checks.zero("Laurent resolvent residuals", f"a={a}, input {j}, N={n}",
                            D(y)-a*y-f+a**(-n)*term)

    term = t
    for k in range(19):
        checks.zero("factorial oscillator", f"D^{k} t",
                    term-(-1)**k*sp.factorial(k)*t**(k+1))
        term = D(term)
    y = sp.S.Zero
    for n in range(1, 17):
        y += (-1)**(n-1)*sp.factorial(2*n-2)*t**(2*n-1)
        expected = (-1)**(n-1)*sp.factorial(2*n)*t**(2*n+1)
        checks.zero("factorial oscillator", f"oscillator residual N={n}", D(D(y))+y-t-expected)

    for polynomial in [1+X**2, 2-3*X+X**2, 1+X+X**3]:
        for n in range(1, 8):
            coefficients = sp.series(1/polynomial, X, 0, n).removeO()
            term, y = t+2*t*t, sp.S.Zero
            for k in range(n):
                y += coefficients.coeff(X, k)*term
                term = D(term)
            term, residual = y, -(t+2*t*t)
            for k in range(sp.degree(polynomial, X)+1):
                residual += sp.expand(polynomial).coeff(X, k)*term
                term = D(term)
            checks.zero("polynomial resolvent cutoffs", f"P={polynomial}, N={n}",
                        trunc(residual, t, n))

    for j, f in enumerate([t**(-4)+3*t, 1+2*t**2, t**3-t**7, sp.Integer(3)], 1):
        exponents = [term.as_powers_dict().get(t, sp.S.Zero)
                     for term in sp.Add.make_args(sp.expand(f))]
        start = min(exponents)
        term = f
        for n in range(9):
            if term == 0:
                valid = True
            else:
                exponents = [q.as_powers_dict().get(t, sp.S.Zero)
                             for q in sp.Add.make_args(sp.expand(term))]
                valid = min(exponents) >= start+n
            checks.condition("Laurent valuation bounds", f"input {j}, derivative {n}", valid)
            term = D(term)

    return checks.finish()


if __name__ == "__main__":
    raise SystemExit(main())
