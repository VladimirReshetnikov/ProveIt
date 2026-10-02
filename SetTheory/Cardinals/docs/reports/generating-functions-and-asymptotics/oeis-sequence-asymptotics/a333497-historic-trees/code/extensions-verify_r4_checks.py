#!/usr/bin/env python3
"""New exact algebra and recurrence checks for r=4 (m=3).

This script checks finite algebraic identities and exact coefficients. It does
not mechanically certify the analytic continuation or nonvanishing arguments.
No floating-point arithmetic is used.
"""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import os
import sympy as sp

OUT = Path(os.environ.get('HISTORIC_TREE_OUTPUT_DIR', Path(__file__).resolve().parent))
a, s, nu, mu = sp.symbols('a s nu mu', positive=True)
p1, p2, p3 = sp.symbols('p1 p2 p3')
field = sp.Matrix([p2-sp.Rational(5,4)*p1**2,
                   p3-sp.Rational(3,2)*p1*p2,
                   1-sp.Rational(7,4)*p1*p3])
equilibrium = {p1:4*a, p2:20*a**2, p3:120*a**3}
A = field.jacobian([p1,p2,p3]).subs(equilibrium)
z = sp.Symbol('z')
char = sp.expand(A.charpoly(z).as_expr())
char_expected = (z+12*a)*(z**2+11*a*z+70*a**2)
lam_plus = (11+sp.I*sp.sqrt(159))/2
lam_minus = sp.conjugate(lam_plus)
checks = {}
checks['normalized_equilibrium_mod_a4_minus_1_over_840'] = all(
    sp.rem(sp.Poly(f,a), sp.Poly(a**4-sp.Rational(1,840),a)).is_zero
    for f in field.subs(equilibrium))
checks['normalized_jacobian_exact'] = A == sp.Matrix([
    [-10*a,1,0],[-30*a**2,-6*a,1],[-210*a**3,0,-7*a]])
checks['normalized_characteristic_factorization_exact'] = sp.expand(char-char_expected)==0
checks['normalized_spectrum_exact'] = all(
    sp.simplify(char.subs(z,ev))==0 for ev in (-12*a,-a*lam_plus,-a*lam_minus))
indicial = sp.prod(j-nu for j in range(4,8))-1680
indicial_expected = (nu+1)*(nu-12)*(nu**2-11*nu+70)
checks['indicial_factorization_exact'] = sp.expand(indicial-indicial_expected)==0
chi = sp.prod(mu+j for j in range(4,8))-1680
checks['fixed_blowup_characteristic_factorization_exact'] = sp.expand(
    chi-(mu-1)*(mu+12)*(mu**2+11*mu+70))==0

# Conserved energy in the original four-dimensional ODE.
u0,u1,u2,u3 = sp.symbols('u0 u1 u2 u3')
energy = u3*u1-u2**2/2-u0**3/3
energy_dot = sum(sp.diff(energy,u)*v for u,v in
                 zip((u0,u1,u2,u3),(u1,u2,u3,u0**2)))
checks['energy_derivative_exactly_zero'] = sp.expand(energy_dot)==0
initial_energy = energy.subs({u0:1,u1:1,u2:1,u3:1})
checks['initial_energy_one_sixth'] = initial_energy==sp.Rational(1,6)

# d/dx = -d/dt. Only the coefficient linear in the pure real-mode D is used.
t,d = sp.symbols('t d', nonzero=True)
H = 840*t**-4*(1+d*t**12)
jet = [(-1)**j*sp.diff(H,t,j) for j in range(4)]
energy_series = sp.expand(energy.subs(dict(zip((u0,u1,u2,u3),jet))))
linear_energy_coefficient = sp.expand(energy_series).coeff(d,1)
checks['pure_leading_energy_zero'] = sp.simplify(energy_series.subs(d,0))==0
checks['linear_real_mode_energy_coefficient_exact'] = linear_energy_coefficient==-4264*840**2
D = sp.cancel(initial_energy/linear_energy_coefficient)
checks['D_exact'] = D==-sp.Rational(1,18052070400)
# Any real semigroup exponent at 12 must satisfy 12*m+11*k=12.
semigroup_solutions = [(m,k) for m in range(2) for k in range(2) if 12*m+11*k==12]
checks['only_pure_real_mode_at_energy_constant'] = semigroup_solutions==[(1,0)]
real_mode_eigenvector = [sp.rf(4-12,j)/sp.rf(4,j) for j in range(4)]
checks['real_mode_strictly_alternating_vector_exact'] = real_mode_eigenvector==[
    sp.Integer(1),sp.Integer(-2),sp.Rational(14,5),-sp.Rational(14,5)]

# Universal leading coefficient normalization, with its r=4 specialization.
r,n = sp.symbols('r n', integer=True, positive=True)
leading_amplitude = sp.factorial(2*r-1)/sp.factorial(r-1)
universal_prefactor = sp.factorial(2*r-1)/sp.factorial(r-1)**2
checks['universal_leading_prefactor_factorization_exact'] = sp.combsimp(
    leading_amplitude*sp.rf(r,n)-universal_prefactor*sp.factorial(n+r-1))==0
checks['r4_leading_prefactor_is_140'] = universal_prefactor.subs(r,4)==140
checks['r4_polynomial_factorization_exact'] = sp.combsimp(
    840*sp.rf(4,n)/sp.factorial(n)-140*(n+1)*(n+2)*(n+3))==0

# Independent exact integer and rational ordinary-EGF recurrences through n=100.
N=100
h=[1,1,1,1]
for j in range(N-3):
    h.append(sum(comb(j,k)*h[k]*h[j-k] for k in range(j+1)))
b=[Fraction(1,factorial(j)) for j in range(4)]
for j in range(N-3):
    b.append(sum((b[k]*b[j-k] for k in range(j+1)),Fraction()) /
             ((j+1)*(j+2)*(j+3)*(j+4)))
checks['exact_count_length_101'] = len(h)==len(b)==101
checks['integer_and_ordinary_egf_recurrences_agree_through100'] = all(
    b[j]*factorial(j)==h[j] for j in range(N+1))
checks['exact_counts_strictly_positive'] = all(x>0 for x in h)
assert all(checks.values()), checks
counts = json.dumps(h)+'\n'
(OUT/'exact_h_r4_0_100.json').write_text(counts)
record = {
    'status':'Exact symbolic and integer/rational arithmetic checks; no fitted constants.',
    'r':4,'m':3,'all_exact_checks_pass':all(checks.values()),'checks':checks,
    'normalized_jacobian':[[str(x) for x in row] for row in A.tolist()],
    'normalized_characteristic_polynomial':str(char),
    'normalized_characteristic_factorization':str(char_expected),
    'lambda_exponents':['12',str(lam_plus),str(lam_minus)],
    'indicial_factorization':str(indicial_expected),
    'conserved_energy':'u3*u1-u2**2/2-u0**3/3',
    'initial_energy':str(initial_energy),
    'linear_real_mode_energy_coefficient':str(linear_energy_coefficient),
    'D':str(D),
    'real_mode_vector':[str(v) for v in real_mode_eigenvector],
    'universal_leading_prefactor':'factorial(2*r-1)/factorial(r-1)**2',
    'r4_leading_prefactor':140,
    'exact_recurrence_nmax':N,
    'exact_counts_sha256':hashlib.sha256(counts.encode()).hexdigest(),
    'exact_first30':h[:30],
}
(OUT/'r4_exact_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: r=4 spectrum, energy, D, indicial/leading factorization, and exact recurrences through100.')
