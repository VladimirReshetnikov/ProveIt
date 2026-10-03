"""Exact symbolic checks for the ordinary I4 pair-convolution evaluation.

Requires SymPy. The analytic integral and differentiation justifications
are supplied in the manuscript, not inferred from this computation.
"""
from pathlib import Path
import json
import sympy as s

x, total, a, A = s.symbols('x total a A', positive=True)
primitive = 2*(2*x-total)/(total**2*s.sqrt(x*(total-x)))
assert s.simplify(s.diff(primitive,x)-(x*(total-x))**(-s.Rational(3,2))) == 0
pair = 4*(2*a-total)/(total**2*s.sqrt(a*(total-a)))
assert s.simplify(primitive.subs(x,a)-primitive.subs(x,total-a)-pair) == 0
J = s.pi*(1-s.sqrt(1-1/A))
I4 = s.simplify(-1728*s.diff(J,A).subs(A,9))
assert s.simplify(I4-8*s.sqrt(2)*s.pi) == 0
B3 = s.simplify(5*I4/(16*s.pi**s.Rational(3,2)))
A3 = s.simplify(4*3**s.Rational(13,2)/(8*s.pi*2))
assert s.simplify(B3-5/s.sqrt(2*s.pi)) == 0
assert s.simplify(A3-729*s.sqrt(3)/(4*s.pi)) == 0
result = dict(status='passed', arithmetic='exact symbolic',
              pair_antiderivative_residual='0', pair_endpoint_residual='0',
              I4=str(I4), B3=str(B3), A3=str(A3),
              scope='Algebra check; the manuscript supplies the ordinary integral proof.')
Path(__file__).with_name('integral_symbolic.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,sort_keys=True))
