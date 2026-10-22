#!/usr/bin/env python3
"""Independent SymPy verification of frozen sparse packets (not source builder)."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]/'domains'
checks=[]
for fn,expected_n,expected_r,degree,cert in [
 ('integer54_quartic.json',54,31,4,{'tau':4}),
 ('integer45_degree6.json',45,22,6,{'Jrep':2,'L':2,'s':2}),
 ('integer39_degree8.json',39,16,8,{'Jrep':6,'s':2})]:
 p=json.loads((ROOT/fn).read_text()); names=p['variables']; const=p.get('fixed_numerals',p.get('fixed_integer_coefficients'))
 env={n:s.Symbol(n) for n in names+const}
 vs=[env[n] for n in names]
 residuals=[s.sympify(r,locals=env) for r in p['residuals']]
 assert len(names)==len(set(names))==expected_n
 assert len(residuals)==expected_r
 assert set().union(*(r.free_symbols for r in residuals))==set(env.values())
 ds=[s.Poly(r,*vs).total_degree() for r in residuals]
 assert max(ds)==degree//2
 poly=s.Poly(sum(r*r for r in residuals).expand(),*vs)
 assert poly.total_degree()==degree
 coefficient=s.factor(poly.coeff_monomial(s.prod(env[v]**e for v,e in cert.items())))
 expected=1 if degree==4 else env['Bm1']**(degree-4 if degree==6 else 6)
 assert coefficient==expected,(fn,coefficient,expected)
 if degree==4:
  parent=json.loads((ROOT/'sources/12-gap-norm14/quadratic/quartic32.json').read_text())
  oldenv={n:s.Symbol(n) for n in parent['variables']+const}
  parent_rs=[s.sympify(r,locals=oldenv) for r in parent['residuals']]
  for orig,new in zip(parent_rs,residuals): assert s.expand(orig.subs({oldenv['i']:2*env['r']+1})-new)==0
  assert s.expand(residuals[23]-(env['w']-env['u']**2))==0
  for v,rs in zip('J F alpha z s eta zeta'.split(),residuals[24:]):
   x,y,z=[env[f'{v}_pos{j}'] for j in (1,2,3)]
   assert s.expand(rs-(env[v]-1-x*x-y*y-z*(z+1)))==0
 if degree>4:
  parent=json.loads((ROOT/p['parent_file']).read_text())
  oldenv={n:s.Symbol(n) for n in parent['variables']+const}
  sub={oldenv['i']:2*env['r']+1}
  sub.update({oldenv[k]:s.sympify(v,locals=env) for k,v in p['direct_substitutions'].items()})
  parent_rs=[s.sympify(r,locals=oldenv) for r in parent['residual_polynomials']]
  for orig,new in zip(parent_rs,residuals): assert s.expand(orig.subs(sub,simultaneous=True)-new)==0
  for v,rs in zip(p['retained_guard_coordinates'],residuals[len(parent_rs):]):
   if v=='w': definition=env['u']**2
   else:
    x,y,z=[env[f'{v}_pos{j}'] for j in (1,2,3)]
    definition=1+x*x+y*y+z*(z+1)
   assert s.expand(rs-(env[v]-definition))==0
 checks.append({'packet':fn,'variables':len(names),'residuals':len(residuals),'max_residual_degree':max(ds),'exact_sos_degree':degree,'certificate_coefficient':str(coefficient),'parent_identity':True})
out={'engine':'Independent SymPy expansion; no import of sparse_poly or builder scripts','checks':checks,'domain_proof_scope':'Human-reviewed signed lift restoration, tau affine shear, transport convention, and odd-i/square-w completeness; inherited Pell/compiler lemmas not re-proved.'}
(Path(__file__).parent/'LOW_DEGREE_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
