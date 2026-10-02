"""Symbolic generic factorial-power inverse; no fitted amplitude is certified."""
import sympy as s
import json
from pathlib import Path
A,L,D,E,p,q,S,d=s.symbols('A L D E p q S d', nonzero=True)
u=-A/S;v=-q/S
w=-L/S+A*A/(3*S*S)-d*A*A/(2*S**3)
r=-D/S+A*(p+q/3)/S**2-d*A*q/S**3
f=-E/S+p*q/S**2-d*(A*L+q*q/2)/S**3+d*A**3/(3*S**4)-d*d*A**3/(2*S**5)
checks=[S*u+A,S*v+q,S*w+d*u*u/2+A*u/3+L,S*r+d*u*v+A*v/3+p*u+D,S*f+d*v*v/2+(d*u+A/3)*w-d*u**3/6-A*u*u/9+p*v-L*u/3+E]
checks=[s.simplify(x) for x in checks]
assert checks==[0]*5
report={'generic_inverse_residual_coefficients':[str(c) for c in checks], 'parameters_kept_symbolic':'A,L,D,E,p,q,S,d','word_stirling_power':'-1/6','word_stirling_inverse_n':'-1/36','total_stirling_power':'-2/3','total_stirling_inverse_n':'209/288','caution':'No numerical amplitude enclosure or unconditional integer rounding claim.'}
Path(__file__).with_name('inverse-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
