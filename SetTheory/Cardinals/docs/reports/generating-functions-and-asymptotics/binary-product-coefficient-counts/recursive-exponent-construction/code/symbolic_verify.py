#!/usr/bin/env python3
"""Optional exact rational-function certificates; requires SymPy."""
from pathlib import Path
import json
import sympy as s

if not __debug__:
    raise RuntimeError("Run without -O: this verifier uses assertions.")

ROOT = Path(__file__).resolve().parents[1]
t, z = s.symbols('t z')
q = 1-t+2*t**2
A = (2-t)/q
Ap = A-2
B = t/(1-2*t)**2 + (1-t)*Ap/(1-2*t)
B_display = (2*t-8*t**2+16*t**3-8*t**4)/((1-2*t)**2*q)
S = (2*t/(1-2*t)+Ap)/(1-2*t)
U = t/q
B_closed = t/(1-2*t)**2-t/(2*(1-2*t))+(5*Ap+7*U)/8
S_closed = 2*t/(1-2*t)**2-1/(2*(1-2*t))+(A+7*U)/4
G = z/(1-2*z*z)+B.subs(t,z*z)
N = z+2*z**2-3*z**3-8*z**4+4*z**5+16*z**6-4*z**7-8*z**8
D = 1-5*z**2+10*z**4-12*z**6+8*z**8
identities = {
    'main_generating_function': s.cancel(B-B_display),
    'full_generating_function': s.cancel(G-N/D),
    'denominator_factorization': s.expand(D-(1-2*z*z)**2*(1-z*z+2*z**4)),
    'main_closed_form': s.cancel(B-B_closed),
    'total_degree_closed_form': s.cancel(S-S_closed),
}
assert all(value == 0 for value in identities.values())
assert s.gcd(N, D) == 1
report = {'sympy_version': s.__version__,
          'identities': {key: str(value) for key, value in identities.items()},
          'numerator_denominator_gcd': str(s.gcd(N,D)),
          'all_checks_passed': True}
(ROOT/'data'/'symbolic_verification.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
