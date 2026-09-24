#!/usr/bin/env python3
"""Optional symbolic audit of the formulas in the article (requires SymPy)."""
from pathlib import Path
import json
import sympy as s

n, m, k = s.symbols("n m k", integer=True)

def check_zero(expr, label):
    if s.cancel(expr) != 0:
        raise AssertionError(label)
    print("PASS:", label)

def prefix_L(a):
    return [s.factor(a[j]**2 - (a[j-1]*a[j+1] if j else 0))
            for j in range(len(a)-1)]

def binom_poly(j):
    return s.prod(n-i for i in range(j))/s.factorial(j)

p = [binom_poly(j) for j in range(8)]
a = [s.Integer(0), n-1] + p[2:]
b = prefix_L(a)
c = prefix_L(b)
d = prefix_L(c)
Q = 2*n**4-12*n**3-327*n**2-412*n+36
S = 4*n**5-27*n**4+186*n**3+145*n**2+684*n-3564
expected = {
    "b1": (n-1)**2,
    "b2": n*(n-1)**2*(n+4)/12,
    "b3": n**2*(n-2)*(n-1)**2*(n+1)/144,
    "b4": n**2*(n-1)**2*(n-2)**2*(n-3)*(n+1)/2880,
    "c1": (n-1)**4,
    "c2": n**2*(n-1)**4*(n+2)/16,
    "c3": n**3*(n-2)**2*(n-1)**4*(n+1)*(n**2+n+18)/51840,
    "d1": (n-1)**8,
    "d2": -n**3*(n-1)**8*(n+4)*Q/103680,
    "d3": n**6*(n-2)**3*(n-1)**8*(n+1)**2*S/10749542400,
}
for name, rhs in expected.items():
    seq = {"b": b, "c": c, "d": d}[name[0]]
    check_zero(seq[int(name[1:])] - rhs, name)
check_zero(Q.subs(n,m+17) - (2*m**4+124*m**3+2529*m**2+17370*m+6615),
           "positive shift Q(17+m)")
check_zero(S.subs(n,m+3) - (4*m**5+33*m**4+222*m**3+1441*m**2+5280*m+3600),
           "positive shift S(3+m)")
B = prefix_L(p)
C = prefix_L(B)
check_zero(b[2] - B[2] - p[3], "b2 = Pascal b2 + binomial(n,3)")
check_zero(c[3] - C[3] + p[3]*B[4], "c3 = Pascal c3 - binomial(n,3)*B4")
check_zero(c[4] - C[4], "unaffected second-iterate tail begins at k=4")
# Rational neighbor ratios for Pascal's first and second iterates.
rB = k*(n-k)/((k+2)*(n-k+2))
rC = k**2*(n-k)**2/((k+1)*(k+3)*(n-k+1)*(n-k+3))
rP = k*(n-k)/((k+1)*(n-k+1))
h = (n+1)/((k+1)*(n-k+1))
g = 2*(n+2)/((k+2)*(n-k+2))
check_zero(rP**2*h.subs(k,k-1)*h.subs(k,k+1)/h**2-rB,
           "first Pascal neighbor ratio")
check_zero(rB**2*g.subs(k,k-1)*g.subs(k,k+1)/g**2-rC,
           "second Pascal neighbor ratio")
poly = s.Poly(d[2], n)
if poly.degree() != 16 or poly.LC() != -s.Rational(1,51840):
    raise AssertionError("Wrong witness degree or leading coefficient")
check_zero(poly.coeff_monomial(n**15)-s.Rational(1,5184), "asymptotic second term")
# JSON numerator data independently recovers the polynomial witness.
data_path = Path(__file__).resolve().parent / "data" / "witness_generating_function.json"
data = json.loads(data_path.read_text())
P = [int(x) for x in data["numerator_coefficients_in_ascending_degree"]]
coeff_formula = sum(P[j] * s.prod(m-j+i for i in range(1,17))/s.factorial(16)
                    for j in range(17))
check_zero(coeff_formula + d[2].subs(n,m+17), "rational generating function")
print("PASS: polynomial witness has degree 16 and leading coefficient -1/51840.")
print("Environment: SymPy", s.__version__)
