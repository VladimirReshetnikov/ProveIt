"""Exact independent Taylor audit of the corrected printed Gamma coefficient."""
from pathlib import Path
import json,sys
import sympy as s
V=Path(__file__).resolve().parent;B=V.parent
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
u,g,z2,z3,z4,z5=s.symbols('u gamma zeta2 zeta3 zeta4 zeta5')
logarithm=g*u-z2*u**2/2+z3*u**3/3-z4*u**4/4+z5*u**5/5
direct=s.expand(s.exp(logarithm).series(u,0,6).removeO()).coeff(u,5)
# Independent recurrence from differentiating exp(logarithm).
c=[s.S.One]
for n in range(1,6):c.append(s.expand(sum(k*logarithm.coeff(u,k)*c[n-k] for k in range(1,n+1))/n))
printed=(g**5-10*g**3*z2+20*g**2*z3+15*g*z2**2-30*g*z4-20*z2*z3+24*z5)/120
assert s.expand(direct-printed)==s.expand(c[5]-printed)==0
wrong_symbol=s.symbols('unassigned_zeta');old=(g**5-10*g**3*z2+20*g**2*z3+15*g*z2**2-30*g*z4-20*z2*z3+24*wrong_symbol*c[5])/120
assert s.expand(old-printed)!=0
text=(B/'chapters/07-digamma-power-moments.tex').read_text(encoding='utf-8')
assert text.count(r'-20\zeta_2\zeta_3+24\zeta_5')==1 and r'24\zeta\alpha_5' not in text
readme=(B/'README.md').read_text(encoding='utf-8');assert readme.count('1,032-input first-letter X family now has an exact top-sector rank of 1,008')==1
out=dict(status='PASS',degree=5,coefficient=str(printed),independent_exponential_and_differentiated_recurrence_agree=True,printed_equation_matches_verified_coefficient=True,wrong_self_referential_term_rejected=True,repeated_readme_passage_count=1,imports_delivered_code=False,scope='Exact degree-five reciprocal-Gamma Taylor coefficient and literal binding to the corrected printed equation. The old undefined zeta/alpha term is rejected. This corrects a printed formula; it does not certify every equation in the manuscript.')
(V/'alpha-five-exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out,indent=2))
