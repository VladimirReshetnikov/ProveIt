"""Independent symbolic large-order coefficients from binomial polynomials."""
import contextlib
import io
import importlib.util
import sys
from pathlib import Path
import sympy as sp

folder = Path(__file__).parent
spec = importlib.util.spec_from_file_location('independent_check', folder/'independent_check.py')
c = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(c)

R = int(sys.argv[1]) if len(sys.argv) > 1 else 4
t, j, x = sp.symbols('t j x')
A = sum(sp.Rational(v.numerator, v.denominator)*t**k
        for k, v in enumerate(c.A[:2*R+1]))
q_minus_one = sum(sp.Rational(v.numerator, v.denominator)*t**k
                  for k, v in enumerate(c.q[:2*R+1]) if k)
ratio_sum = sp.S(0)
terms = []
for m in range(2*R+1):
    F = sp.S(0)
    falling = sp.S(1)
    for p in range(m//2+1):
        if p:
            falling *= (j-p+1)/p
        coeff = sp.expand(A*q_minus_one**p).coeff(t, m)
        F += falling*coeff
    F = sp.expand(F)
    degree = R+m//2
    ratio = [c.F(1)] + [c.F(0)]*degree
    for a in range(m):
        left = [c.F(2*a+3, 2)**r for r in range(degree+1)]
        right = [c.F(2*a-1, 2)**r for r in range(degree+1)]
        factor = c.mul(c.mul([c.F(0), c.F(4), c.F(-4*a)], left, degree), right, degree)
        ratio = c.mul(ratio, factor, degree)
    ratio_poly = sum(sp.Rational(v.numerator, v.denominator)*x**r
                     for r, v in enumerate(ratio))
    full_term = sp.expand(ratio_poly*sp.expand(F.subs(j, 1/x-m)))
    term = sum(full_term.coeff(x, r)*x**r for r in range(R+1))
    ratio_sum += term
    terms.append((m, F, term))

ratio_sum = sp.expand(ratio_sum)
result = '\n'.join([
    'Asymptotic expansion of h_k / (-b_k), x=1/k:',
    str(ratio_sum),
    '',
    *[f'm={m}: F_m(j)={F}; contribution={term}' for m, F, term in terms],
    '',
])
(folder/'asymptotic_check.txt').write_text(result)
print(result)
