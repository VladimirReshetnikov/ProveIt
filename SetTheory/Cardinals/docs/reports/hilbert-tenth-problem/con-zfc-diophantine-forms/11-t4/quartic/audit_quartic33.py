"""Independently authored symbolic audit; does not execute downloaded code."""
import json
from pathlib import Path
import sympy as S

HERE = Path(__file__).resolve().parent
names = 'J F alpha z f h i o s w tau eta zeta y gamma N E P c a X D A G L R V g I B U H j'.split()
v = dict(zip(names, S.symbols(' '.join(names))))
globals().update(v)
beta, K, MC, MF = S.symbols('beta K MC MF')
q = beta*J + 1
k = eta + zeta
equations = [
    ('L', 'q**2-1'),
    ('N', '(L+1)*q'),
    ('X', 'w*q'),
    ('a', 'E+N*s'),
    ('E', 'X*(a-E)'),
    ('c', 'eta+(a-E)*k'),
    ('P', 'E*(c-eta)+k'),
    ('tau**2', 'P*(P-k)+1'),
    ('D', 'X+a*c+gamma*(4*a+3)'),
    ('A', 'D**2-1'),
    ('U', '(a+1)*c'),
    ('A', 'U*(U+2*c)'),
    ('k', 'E*h+R+1'),
    ('G', '(q-1)*(q-F)+alpha'),
    ('R', 'G*L+J*(MC+q*MF)'),
    ('(K+w)*(q-F-alpha)+q-F-z*(q-1)', '1'),
    ('H', '(a+1)*(f-1)'),
    ('V', 'o*f-c'),
    ('V', 'j*c-R'),
    ('g', 'y**2-V**2'),
    ('I', 'A*i'),
    ('B', 'I**2'),
    ('B', 'H*(H+2*a+2*f+4)'),
    ('y**2-B*g', '1'),
]
loc = dict(v, beta=beta, K=K, MC=MC, MF=MF, q=q, k=k)
residuals = [S.expand(S.sympify(l, locals=loc)-S.sympify(r, locals=loc)) for l,r in equations]
degrees = [S.Poly(r, *v.values()).total_degree() for r in residuals]
assert len(names) == len(set(names)) == 33
assert len(residuals) == 24 and max(degrees) == 2
assert S.expand(sum(r*r for r in residuals)).coeff(tau,4) == 1
Delta = a*a+4*a+3
assert S.expand(((a+1)*c)*((a+1)*c+2*c)-Delta*c*c) == 0
assert S.expand(((a+1)*(f-1))*((a+1)*(f-1)+2*a+2*f+4)-Delta*(f*f-1)) == 0

# The quotient identities are checked in the polynomial quotient by
# the normalized strong equation f^2-1-Delta*i^2*c^4=0.
old_o = S.symbols('old_o')
strong = f*f-1-Delta*i*i*c**4
Vmerged = c*(old_o*f-1)-R*f*f
onew = c*old_o-R*f
jnew = old_o*f-R*Delta*i*i*c**3-1
assert S.expand(Vmerged-(onew*f-c)) == 0
assert S.expand(Vmerged-(jnew*c-R)+R*strong) == 0
# Reverse: c*old_o=o+R*f, with integrality proved in the report.
assert S.expand(Vmerged.subs(old_o,(o+R*f)/c)-(o*f-c)) == 0

payload = {
  'description': '24 quadratic equations in 33 strictly positive integer unknowns; exact positive-solution equivalence to packet 08 normalized-strong system.',
  'source_commit': '3b201cdea32d2c816f5f3d20734051f25fd3ef14',
  'source_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/08-start-only67',
  'selected_coefficient_recipe':'../bridge/T4_CONSTANTS.json',
  'coefficient_contract': 'beta=Bm1, K=Kconstant, MC=MC, MF=MF_native+B-1 in the pinned Start-only coefficient ordering. Coefficients are fixed integers, not variables.',
  'variable_domain': 'strictly positive integers',
  'variables': names,
  'variable_count': len(names),
  'equation_count': len(equations),
  'linear_abbreviations': {'q':'beta*J+1','k':'eta+zeta'},
  'equations': [l+' = '+r for l,r in equations],
  'residuals': list(map(str,residuals)),
  'residual_degrees': degrees,
  'single_equation': 'sum(residual**2 for residual in residuals) = 0',
  'single_equation_exact_degree': 4,
  'new_construction': True,
  'claim_limits': 'An explicit upper bound, not global minimality. Inherits packet 08 machine/compiler/Pell correctness, without needing the weaker ordinary-strong rank lemma.'
}
(HERE/'quartic33_normalized.json').write_text(json.dumps(payload,indent=2)+'\n')
receipt = {
  'variables':len(names), 'equations':len(equations), 'max_equation_degree':max(degrees),
  'quartic_exact_degree':4, 'tau_fourth_coefficient':1,
  'factorization_identities':'passed', 'quotient_identities':'passed',
  'positivity_and_integrality':'ordinary mathematical argument in quartic33_proof.md; not decided by numerical search',
  'received_code_executed':False,
}
(HERE/'quartic33_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
