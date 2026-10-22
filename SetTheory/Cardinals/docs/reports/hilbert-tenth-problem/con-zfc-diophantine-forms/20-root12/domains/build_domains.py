#!/usr/bin/env python3
"""Exact sparse audit: 54-integer quartic and 46-integer octic.

These are arithmetic/degree checks. The solvability proof, including all
signed-domain hypotheses, is in DOMAIN_REDUCTION_PROOF.md.
"""
import json
import hashlib
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from instance_binding import binding
from sparse_poly import Poly
ROOT=Path(__file__).resolve().parent
PIN='f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
BASE=ROOT/'sources/12-gap-norm14/quadratic/quartic32.json'
source=json.loads(BASE.read_text())
names=source['variables']
constants=['beta','K0','MC','MF']
env={name:Poly.var(name) for name in names+constants}
res=[eval(s,{'__builtins__':{}},env) for s in source['residuals']]
assert len(names)==32 and len(res)==23
GUARDS='J F alpha z s eta zeta'.split()
sub_odd={'i':2*Poly.var('r')+1}
base=[p.substitute(sub_odd) for p in res]
quad_names=[('r' if n=='i' else n) for n in names]+['u']
quad=base+[Poly.var('w')-Poly.var('u')**2]
for v in GUARDS:
    us=[f'{v}_pos{j}' for j in (1,2,3)]
    quad_names+=us
    x,y,z=map(Poly.var,us)
    quad.append(Poly.var(v)-1-x*x-y*y-z*(z+1))
assert len(quad_names)==54 and len(quad)==31
assert len(set(quad_names))==len(quad_names)
assert max(p.degree(quad_names) for p in quad)==2
assert set().union(*(p.symbols for p in quad))==set(quad_names+constants)
# Exact fourth-degree certificate, independent of coefficient values.
quartic=sum((p*p for p in quad),Poly(0))
assert quartic.degree(quad_names)==4
assert quartic.terms[(('tau',4),)]==1
# All omitted guard coordinates are substitutions, not additional unknowns.
octic_names=[]
octic_sub=dict(sub_odd,w=Poly.var('u')**2)
for v in names:
    if v in GUARDS:
        us=[f'{v}_pos{j}' for j in (1,2,3)]
        octic_names+=us
        x,y,z=map(Poly.var,us)
        octic_sub[v]=1+x*x+y*y+z*(z+1)
    else:
        octic_names.append({'i':'r','w':'u'}.get(v,v))
octic_res=[p.substitute(octic_sub) for p in res]
assert len(octic_names)==46 and len(octic_res)==23
assert max(p.degree(octic_names) for p in octic_res)==4
assert set().union(*(p.symbols for p in octic_res))==set(octic_names+constants)
octic=sum((p*p for p in octic_res),Poly(0))
assert octic.degree(octic_names)==8
# Coefficient of beta^4*J_pos1^8 is 2 (first and G residual squares), so exact degree 8.
assert octic.terms[(('J_pos1',8),('beta',4))]==2
# Eliminating the retained guards and w in quartic residuals is exactly octic.
assert all(a.substitute(octic_sub)==b for a,b in zip(quad[:23],octic_res))
assert all(a.substitute(octic_sub)==0 for a in quad[23:])

def terms(p):
    return [{'coefficient':c,'powers':dict(m)} for m,c in sorted(p.terms.items())]

def packet(kind,vars,res,degree,full):
    return {
        'name':kind,'domain':'unrestricted integers','variable_count':len(vars),
        'variables':vars,'fixed_integer_coefficients':constants,
        'coefficient_binding':binding(constants),
        'historical_source_provenance':{
            'repository':'VladimirReshetnikov/ProveIt','commit':PIN,
            'recipe':'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/14-integer29/vendor/blank67/compiler_constants.py',
            'local_recipe':'ORIGINAL_COEFFICIENTS.json',
            'aliases':{'beta':'Bm1 = B-1','K0':'Kconstant','MC':'MC','MF':'MF (shifted source port)'},
            'warning':'Use one coherent coefficient tuple; the direct square-scale proof here is for the original blank67 five-adic compiler. Do not mix different compiler constants.'
        },
        'number_of_equations':len(res),'residuals':[str(p) for p in res],
        'residual_degrees':[p.degree(vars) for p in res],
        'single_polynomial':'sum of the squares of all listed residuals',
        'exact_total_degree':degree,'sparse_polynomial':terms(full),
        'proof':'DOMAIN_REDUCTION_PROOF.md',
        'verification_scope':'Exact polynomial, variable and degree checks; ordinary mathematical proof relative to pinned Pell/compiler dependencies, not new kernel-checked verification.'
    }
for name,vars,rs,d,full in [('integer54_quartic',quad_names,quad,4,quartic),('integer46_octic',octic_names,octic_res,8,octic)]:
    (ROOT/(name+'.json')).write_text(json.dumps(packet(name,vars,rs,d,full),indent=2)+'\n')
receipt={
    'source_commit':PIN,'source_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),
    'quartic':{'variables':54,'quadratic_equations':31,'exact_degree':4,'expanded_terms':len(quartic.terms),'tau4_coefficient':1},
    'octic':{'variables':46,'equations':23,'max_residual_degree':4,'exact_degree':8,'expanded_terms':len(octic.terms),'beta4_Jpos1_8_coefficient':2},
    'elimination_identity':True,
    'domains':'All listed variables range independently over Z; no retained sign conditions.',
    'comparison':{'prior_integer_quartic':60,'new_integer_quartic':54,'prior_direct_integer_octic_for_quartic32':50,'new_integer_octic':46},
    'scope':'Arithmetic identity and degree certification only; logical proof in companion note.'
}
(ROOT/'DOMAIN_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
