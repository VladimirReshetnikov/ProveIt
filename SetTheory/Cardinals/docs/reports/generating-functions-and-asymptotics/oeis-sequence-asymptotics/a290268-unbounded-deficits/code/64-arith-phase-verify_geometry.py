"""Exact obstruction to a root-geometry-only nonvanishing argument."""
import sympy as s
u=s.symbols('u')
F=u*s.prod(u*u-j*j for j in range(1,7));Q=5369*u*u+3600
checks=[s.expand(F).coeff(u,1)==518400,s.expand(F).coeff(u,3)==-773136,s.expand(F*Q).coeff(u,3)==0,s.expand(F*(4*u*u+14)).coeff(u,3)==-8750304]
if not all(checks):raise ArithmeticError('geometric obstruction identity failed')
print('PASS: exact geometric obstruction and nonzero prescribed-recurrence comparison')
