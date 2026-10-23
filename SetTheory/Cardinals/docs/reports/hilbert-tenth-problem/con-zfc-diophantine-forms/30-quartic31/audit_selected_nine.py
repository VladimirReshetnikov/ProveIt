"""New-owned selected-candidate audit, independent degree and full recipe replay."""
import sys,json,hashlib,random
from pathlib import Path
if not __debug__:raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'review'));sys.path.insert(0,str(R/'nine'))
import audit_modified_nine as degree
from prepare_coefficients import prepare
from optimize_nine_circuit import audit_body,evaluate
from build_compact_nine import index_bound
from independent_review_audit import leading_audit
p=json.loads((R/'arithmetic/quartic31.json').read_text());c,shift=prepare(p)
frozen=json.loads((R/'nine/nu31/COMPACT_CONSTANTS.json').read_text());manifest=json.loads((R/'compiler/COMPACT_COEFFICIENT_BINDING.json').read_text());c,b=index_bound(c,manifest)
assert c['coefficient_records']==frozen['coefficient_records'] and c['nu']==31 and c['L']==5**32 and c['index_exponent']==45933757
assert shift==json.loads((R/'nine/nu31/shifted_quartic.json').read_text())
assert b==json.loads((R/'nine/nu31/INDEX_BOUND_CERTIFICATE.json').read_text())
assert hashlib.sha256((R/'arithmetic/quartic31.json').read_bytes()).hexdigest()==frozen['parent_sha256']
body=json.loads((R/'nine/nu31/nine_compact_magnitude_tight.json').read_text());a=audit_body(body);assert a['live_operations']==1840 and a['fixed_leaves']==404 and a['variable_leaves']==9
v,unresolved=degree.lead_values(body);names={k:v[i] for k,i in body['named_nodes'].items()};leaves={x['name']:v[i] for i,x in enumerate(body['nodes']) if x['kind'] in ('fixed','variable')};alt=degree.alternative(names,leaves)
assert alt['output_rewritten'].degree==120724*5**32+366
mono=list(degree.zero);mono[degree.fixed.index('z_index')]=2
assert alt['output_rewritten'].coeff=={tuple(mono):2**274}
# Every intermediate delta identity is also checked on independent signed modular leaves.
rng=random.Random(312204);count=0
for prime in (101,1009,65537):
 for _ in range(20):
  f={x:rng.randrange(prime) for x in degree.fixed};w={x:rng.randrange(prime) for x in body['variables']};ev=evaluate(body,f,w,prime);ns={k:ev[i] for k,i in body['named_nodes'].items()};z=degree.alternative(ns,{**f,**w})
  for key,bar,plain in [('deltaA','Abar','A'),('deltaC','Cbar','C'),('deltaJ','Jbar','J'),('deltaD','Dbar','D'),('deltaE','Ebar','E'),('deltaF','Fbar','F'),('deltaG','Gbar','Gp'),('deltaH','Hbar','H')]:assert z[key]%prime==(ns[bar]-ns[plain])%prime;count+=1
  assert z['V1square_minus_a1']%prime==(ns['V1']**2-ns['a1'])%prime;assert z['output_rewritten']%prime==ev[body['output']]
control=leading_audit(R/'review/nine_optimized/nine_generic32_majorant.json');assert control['exact_degree']==161844*5**33+484
print(json.dumps(dict(status='PASS',coefficient_records=402,nu=31,degree=alt['output_rewritten'].degree,leader='2^274*z_index^2',circuit=a,cancellation_identity_comparisons=count,baseline32_exact_degree=control['exact_degree']),indent=2))
