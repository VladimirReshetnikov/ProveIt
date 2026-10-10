"""Additional class-number-one and Weber arithmetic certificates."""
from pathlib import Path
import hashlib, importlib.util, json, sys
import mpmath as mp
import sympy as sp
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/relation-cm-zero-transitions/code/cm_norms.py'
spec=importlib.util.spec_from_file_location('additional_cm_intervals',source)
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
mp.iv.dps=120
c.H[8]=c.X-8000;c.H[16]=c.X-287496
certs=[]
for d,j in [(8,8000),(16,287496)]:
    assert len(c.reduced_forms(d))==1
    certificate=c.polynomial_certificate(d)
    certs.append(dict(discriminant=-d,j=j,certificate=certificate))
Y=sp.Symbol('Y')
P=Y**3+155*Y**2+650*Y+23375
assert sp.resultant(P,Y**3-c.X,Y)==-c.H[23]
# The sign above follows the stated resultant ordering; the roots are exact.
weber=c.H[39].subs(c.X,Y**3)
witness=None
for p in list(sp.primerange(5,500)):
    poly=sp.Poly(weber,Y,modulus=p)
    if poly.is_irreducible:
        witness=dict(prime=p,degree=poly.degree(),coefficients=[int(v)%p for v in poly.all_coeffs()]);break
assert witness is not None,'Need a different irreducibility certificate'
report=dict(status='PASS',class_number_one_certificates=certs,
    weber23_polynomial=str(P),weber23_cubing_resultant_exact=True,
    weber39_irreducibility_witness=witness,
    interval_source='../'+source.relative_to(B.parent).as_posix(),
    interval_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    scope='The two interval class polynomials use CM integrality and directed mpmath.iv operations. The Weber resultant and finite-field irreducibility are exact arithmetic certificates.')
(B/'verification/CM-single-Weber.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('PASS: two additional class polynomials; Weber cube image and degree-12 obstruction; prime',witness['prime'])
