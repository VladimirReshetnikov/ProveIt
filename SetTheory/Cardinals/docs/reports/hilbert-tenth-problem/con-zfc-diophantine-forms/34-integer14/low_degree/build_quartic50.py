"""Exact elimination of G from the pinned signed quartic51. Newly authored audit."""
import json, hashlib
from pathlib import Path
import sympy as S

ROOT = Path(__file__).resolve().parent
source = ROOT / 'upstream/integer51_degree4_odd_scale.json'
p = json.loads(source.read_text())
names = p['variables'] + p['fixed_numerals']
syms = dict(zip(names, S.symbols(' '.join(names))))
r = [S.sympify(x, locals=syms) for x in p['residuals']]
J,F,alpha,N,L,G,beta,MC,MF,E,h,eta,zeta = [syms[n] for n in
    'J F alpha N L G beta MC MF E h eta zeta'.split()]
q = beta*J+1
C = q-F-alpha
gvalue = q*(q-F)-C
packing = (q-F)*(N-q)-C*L+(MC+q*MF)*J
new = eta+zeta-1-h*E-packing
assert S.expand(r[12]-(G-gvalue)) == 0
assert S.expand((r[13].subs(G,gvalue)-new)-(q-F)*r[1]) == 0
out = [S.expand(new) if i==13 else rr for i,rr in enumerate(r) if i!=12]
variables = [n for n in p['variables'] if n!='G']
vs = [syms[n] for n in variables]
degrees = [S.Poly(rr,*vs).total_degree() for rr in out]
assert len(variables)==50 and len(out)==29 and max(degrees)==2
assert all(syms['G'] not in rr.free_symbols for rr in out)
assert set(variables) <= set().union(*(set(str(v) for v in rr.free_symbols) for rr in out))
sos = S.Poly(S.expand(sum(rr**2 for rr in out)),*vs)
assert sos.total_degree()==4
mono = [0]*50
mono[variables.index('tau')]=4
assert sos.coeff_monomial(tuple(mono))==1
result = {
 'name':'quartic50_packing_elimination', 'domain':'unrestricted integers',
 'variables':variables, 'variable_count':50, 'equation_count':29,
 'fixed_numerals':p['fixed_numerals'],
 'coefficient_binding':{'manifest': '../COEFFICIENT_BINDING.json', 'compiler_manifest': '../coefficients/payloads/COEFFICIENT_BINDING.json', 'mask_convention': 'shifted source MF', 'transfer_proof': '../coefficients/COEFFICIENT_PROOF.md'},
 'residuals':[str(rr) for rr in out], 'residual_degrees':degrees,
 'single_polynomial':'sum of squares of listed residuals', 'exact_degree':4,
 'exact_degree_certificate':'coefficient of tau^4 is 1',
 'parent_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'source_pin':'8c6eec9d19ef80538c8e61ff6e0180040583446a',
 'proof':'QUARTIC50_PROOF.md',
 'status':'Mathematical equivalence proof; not a new kernel certificate.'}
(ROOT/'quartic50.json').write_text(json.dumps(result,indent=2)+'\n')
receipt={'variables':50,'equations':29,'exact_degree':4,
 'expanded_terms':len(sos.terms()),'symbolic_packing_identity':True,
 'unchanged_residuals':28,'tau_fourth_coefficient':1,
 'parent_sha256':result['parent_sha256']}
(ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
