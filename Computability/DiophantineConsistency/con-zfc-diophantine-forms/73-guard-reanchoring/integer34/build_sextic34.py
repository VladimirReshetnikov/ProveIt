#!/usr/bin/env python3
"""Literal specification of the 34-integer sextic; standard library only."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
q = '(beta*J+1)'
F = f'((K0+4*w_scale)*C-z*({q}-1))'
k = '(eta+zeta)'
H = '(4*a+3)'
pos = lambda prefix: f'({prefix}1**2+{prefix}2**2+{prefix}3*({prefix}3+1)+1)'
rows = [
    ('radix_cube', f'N-{q}**3'),
    ('power_scale', f'2*u**2-4*w_scale*{q}'),
    ('ordinate', 'a-E-(2*v_scale+1)*N'),
    ('product', '2*u**2*(E-a)+E'),
    ('main_ordinate', f'c-eta+(E-a)*{k}'),
    ('first_norm', f'tau_gap**2+(2*tau_gap-{k})*E*(c-eta)-1'),
    ('main_root', f'D-2*u**2-a*c-gamma*{H}'),
    ('discriminant', 'Delta-a**2-4*a-3'),
    ('main_norm', 'D**2-Delta*c**2-1'),
    ('packed_rank', f'{k}-1-h*E-(({q}-{F})*(N-{q})-C*({q}**2-1)+(MC+{q}*MF)*J)'),
    ('first_quotient', 'V+c-f*o'),
    ('second_quotient', f'-E*h+V-c*j+{k}-1'),
    ('strong_multiple', 'I-(2*r+1)*c**2'),
    ('auxiliary_square', 'Baux-I**2'),
    ('strong_norm', 'Baux-Delta*(f**2-1)'),
    ('auxiliary_norm', 'Baux*(V**2-y**2)+y**2-1'),
    ('common_sign_CA', f'C*({q}-{F}-C)-{pos("CA_pos")}'),
    ('common_sign_FC', f'{F}*C-{pos("FC_pos")}'),
    ('common_sign_eta_zeta', f'eta*zeta-{pos("eta_zeta_pos")}'),
]
variables = ['J','C','z','f','h','r','v_scale','w_scale','tau_gap',
 'eta','zeta','y','gamma','o','j','N','E','c','a','D','V','I','Baux','Delta','u',
 'CA_pos1','CA_pos2','CA_pos3','FC_pos1','FC_pos2','FC_pos3',
 'eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3']
restoration = dict(
 alpha=f'{q}-{F}-C', F=F, L=f'{q}**2-1', X='2*u**2',
 C2='c**2', F2='f**2', g='y**2-V**2', P=f'{k}+E*(c-eta)',
 tau='tau_gap+E*(c-eta)')
obj = {
 'name':'sextic34_transport_pivot', 'domain':'unrestricted integers',
 'variables':variables, 'variable_count':len(variables),
 'fixed_numerals':['beta','K0','MC','MF'],
 'residual_labels':[name for name,_ in rows],
 'residuals':[expr for _,expr in rows], 'equation_count':len(rows),
 'single_polynomial':'sum of squares of the 19 listed residuals',
 'exact_degree':6, 'degree_certificate':'coefficient of r^2*c^4 is exactly 4',
 'source':{
  'commit':'9cca523d9f27ad39d52993f4065cbd7e58f8bdd4',
  'path':'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json',
  'git_blob_sha1':'521f16a310f49e736ea8ffac3fe13847ff71adcb',
  'local_path':'upstream/quartic41.json'},
 'coefficient_binding':{
  'backend':'mixed-parity-unrounded-1064921',
  'mask_convention':'MF is already shifted by beta',
  'policy':'Use precisely the complete four-port tuple of the source quartic41.'},
 'restoration_except_positivity_witnesses':restoration,
 'guard_change':{
  'old':['F*alpha>0','F*C>0'], 'new':['C*alpha>0','F*C>0'],
  'justification':'Both assert F, alpha, C have the same nonzero sign; the ternary positivity witnesses are reselected, not equated.'},
 'proof_status':'Exact algebraic reduction and ordinary proof relative to the identified source Q41 theorem; no new end-to-end formal certificate.'
}
(ROOT/'sextic34.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'variables':len(variables),'residuals':len(rows),'file':'sextic34.json'}))
