#!/usr/bin/env python3
"""Second exact symbolic resultant certificate for the double-chain quartic.

This eliminates a different pair from code/derive_quartic.py: here the two
polynomials are the quadratic satisfied by a = g(w,t) and the relation
satisfied by F = a*g(-w,t), as displayed in the article after Corollary 5.3.
The result is an identity computation, not a finite truncation in z or t:
the difference from the printed quartic is the zero polynomial.

Optional: requires SymPy. Neither the proofs nor code/verify.py need it.
"""
from pathlib import Path
import json
import sympy as sp

t, w, a, T = sp.symbols('t w a T')
p = t*w**2*a**2 + ((1+t)*w-1)*a + 1
r = a**2 - ((1+t)*w+1)*T*a + t*w**2*T**2
resultant = sp.resultant(p, r, a)
target = (t**4*w**8*T**4
          + t**2*w**4*((1+t)**2*w**2-1)*T**3
          + 2*t*w**2*(1+(t**2+t+1)*w**2)*T**2
          + ((1+t)**2*w**2-1)*T + 1)
residual = sp.Poly(resultant-target, t, w, T)
if not residual.is_zero:
    raise ArithmeticError('The resultant does not match the stated quartic')
report = {'status': 'PASS', 'sympy_version': sp.__version__,
          'certificate': 'resultant_a(p,r) - target is the zero polynomial',
          'p': str(p), 'r': str(r),
          'target_before_w_squared_equals_z': str(target),
          'residual': str(residual.as_expr())}
out = Path(__file__).resolve().parents[1]/'results'/'symbolic_certificate.json'
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
