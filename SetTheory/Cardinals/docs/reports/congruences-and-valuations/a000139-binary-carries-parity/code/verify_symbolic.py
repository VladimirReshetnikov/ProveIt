#!/usr/bin/env python3
"""Optional exact symbolic checks. Requires SymPy; no network access."""
from pathlib import Path
import json
import sympy as s

z, y, L, u = s.symbols("z y L u")
M = s.Matrix([[1, 1, 0], [1, 0, y], [0, y, y]])
f = s.Matrix([1, 1, y])
D = 1 - (1 + y)*z - (y*y - y + 1)*z*z + y*(y + 1)*z**3
N = y + (1 - y*y)*z - y**3*z*z + y*(y - 1)**2*z**3
V = N/D
d = 1 - z - z*z
assert s.expand((s.eye(3) - z*M).det() - D) == 0
core = (s.eye(3) - z*M).inv()*f
C = (1 + z)*(1 - y*z)/D
R = (1 - y*z + y*y*z*(1 - z))/D
assert s.cancel(core[0] - C) == 0
assert s.cancel(core[1] - R) == 0
partition = y + y*z*C + z + z*z*C + y*z*z/(1-z) + y*z**3*R/(1-z)
assert s.cancel(partition - V) == 0
assert s.expand(D - ((1-y*z)*d-y*y*z*z*(1-z))) == 0

# Formal y-coefficients, versus the finite closed expression.
H = []
num = [s.expand(N).coeff(y, j) for j in range(4)]
def J(r):
    if r < 0:
        return s.Integer(0)
    return z**r * sum(s.binomial(r-j, j)*(1-z)**j/d**(j+1)
                     for j in range(r//2+1))
for r in range(13):
    v = num[r] if r < 4 else s.Integer(0)
    if r:
        v += z*d*H[r-1]
    if r >= 2:
        v += z*z*(1-z)*H[r-2]
    H.append(s.cancel(v/d))
    closed = sum(num[j]*J(r-j) for j in range(4))
    assert s.cancel(H[r]-closed) == 0
    denominator = s.denom(H[r])
    assert s.degree(denominator, z) == 2*(r//2+1)
assert s.cancel(H[0]-z/d) == 0
assert s.cancel(H[1]-(1+z*z+z**3)/d) == 0
assert s.cancel(H[2]-z**4*(1-z*z)/d**2) == 0
assert s.cancel(H[3]-z**3*(1-z*z)*(1+z+z*z)/d**2) == 0

first = (-s.Rational(7,6)/(1-2*z) + s.Rational(1,2)/(1-2*z)**2
         + s.Rational(1,6)/(1+z) + s.Rational(3,2)/(1-z))
second = (1-s.Rational(17,18)/(1-2*z)-1/(1-2*z)**2
          + s.Rational(1,2)/(1-2*z)**3-s.Rational(13,18)/(1+z)
          + s.Rational(1,6)/(1+z)**2-s.Rational(1,2)/(1-z)
          + s.Rational(3,2)/(1-z)**2)
assert s.cancel(s.diff(V,y).subs(y,1)-first) == 0
assert s.cancel(s.diff(V,y,2).subs(y,1)-second) == 0

char = M.charpoly(L).as_expr()
trial = 2 + u + s.Rational(2,3)*u*u-s.Rational(1,3)*u**3-s.Rational(7,27)*u**4
assert s.series(char.subs({L:trial, y:1+u}),u,0,5).removeO() == 0
K = s.series(s.log(trial.subs(u,s.exp(u)-1)/2),u,0,5).removeO().expand()
assert s.expand(K-(u/2+s.Rational(11,24)*u*u-s.Rational(569,1728)*u**4)) == 0
swap = s.Matrix([[0,0,1],[0,1,0],[1,0,0]])
assert swap*M*swap == y*M.subs(y,1/y)

report = {"sympy":s.__version__,"all_tests_passed":True,
          "fixed_level_range":[0,12],
          "identities":["carry matrix determinant", "resolvent C and R",
                        "full valuation generating function", "split denominator",
                        "finite fixed-level formulas and denominator degrees",
                        "first and second moment partial fractions",
                        "dominant eigenvalue through degree 4",
                        "cumulant growth through degree 4", "reciprocal spectral symmetry"]}
out=Path(__file__).resolve().parents[1]/"data"/"symbolic_verification.json"
out.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
