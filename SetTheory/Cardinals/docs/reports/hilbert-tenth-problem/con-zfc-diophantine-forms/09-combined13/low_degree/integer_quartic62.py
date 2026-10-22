#!/usr/bin/env python3
"""Emit a 62-integer-variable quartic from the partially signed 32-variable core."""
import json
from pathlib import Path
import quartic32 as source
from sparse_polynomial import Ring, Polynomial

POSITIVE_PRIMARY = 'J F alpha z i s w eta zeta gamma'.split()
CONSTANTS = ['beta','K0','MC','MF']
AUX = [name+'_'+suffix for name in POSITIVE_PRIMARY for suffix in ['u','v','w']]
NAMES = source.NAMES + AUX
ring = Ring(NAMES+CONSTANTS)

def lift(poly):
    terms={}
    for monomial,coefficient in poly.terms.items():
        powers=dict(zip(poly.ring.names,monomial))
        terms[tuple(powers.get(name,0) for name in ring.names)]=coefficient
    return Polynomial(ring,terms)

residuals=[lift(r) for r in source.residuals]
labels=[x[0] for x in source.equations]
for name in POSITIVE_PRIMARY:
    x,u,v,w=(ring.variables[key] for key in [name,name+'_u',name+'_v',name+'_w'])
    residuals.append(x-1-u*u-v*v-w*(w+1))
    labels.append(f'{name} = 1+{name}_u^2+{name}_v^2+{name}_w({name}_w+1)')

assert len(NAMES)==62 and len(set(NAMES))==62
assert len(residuals)==33
assert all(r.degree(len(NAMES))==2 for r in residuals)
assert all(('tau' in r.free_variables())==(i==7) for i,r in enumerate(residuals))
assert residuals[7].coefficient({'tau':2})==1
assert set().union(*(r.free_variables() for r in residuals))==set(ring.names)

packet={
 'name':'ordinary-retained-integer-quartic62',
 'domain':'all 62 unknowns range independently over Z',
 'fixed_numerals':CONSTANTS,
 'constant_recipe':'The four-port arithmetic interface is inherited from 06-blank67. The default final binding is ../COEFFICIENT_BINDINGS.json, selecting compiler/tshape_constants.json from the package root, with MF shifted.',
 'coefficient_binding':source.COEFFICIENT_BINDING,
 'variables':NAMES,
 'positive_primary_coordinates_enforced':POSITIVE_PRIMARY,
 'primary_coordinates_allowed_signed':['f','h','o','j','tau','y'],
 'signed_core_proof':'../proofs/SIGNED_CORE_AND_INTEGER62.md',
 'sparse_term_coordinate_order':list(ring.names),
 'equations':[{'number':i+1,'equation':label,'residual':str(poly),
               'degree':poly.degree(len(NAMES)),'terms':poly.json_terms()}
              for i,(label,poly) in enumerate(zip(labels,residuals))],
 'single_polynomial':'sum of squares of the 33 displayed residuals',
 'exact_degree':4,
 'degree_certificate':'Only residual8 contains tau, and its tau^2 coefficient is1, hence the quartic tau^4 coefficient is1.',
 'formal_status':'Mathematical proof and exact finite algebra audit, not a new proof-assistant certificate.'
}
receipt={
 'coefficient_binding':source.COEFFICIENT_BINDING,
 'integer_variables':len(NAMES),'quadratic_equations':len(residuals),
 'positive_primary_coordinates':POSITIVE_PRIMARY,
 'all_residual_degrees':2,'quartic_degree':4,'tau4_coefficient':1,
 'all_ports_live':True,
 'dependency':'The signed ordinary-strong theorem in ../proofs/SIGNED_CORE_AND_INTEGER62.md.'
}
if __name__=='__main__':
    root=Path(__file__).resolve().parent
    (root/'integer_quartic62.json').write_text(json.dumps(packet,indent=2)+'\n')
    (root/'integer_quartic62_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
