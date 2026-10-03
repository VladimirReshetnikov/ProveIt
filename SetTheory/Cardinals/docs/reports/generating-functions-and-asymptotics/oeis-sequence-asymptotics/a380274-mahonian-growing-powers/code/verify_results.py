"""Check recorded computational regressions; this does not certify asymptotic bounds."""
from pathlib import Path
import json, hashlib
from decimal import Decimal
P=Path(__file__).resolve().parent
producer=json.loads((P/'numerical_checks.json').read_text())
audit=json.loads((P/'audit_independent_results.json').read_text())
endpoint=json.loads((P/'endpoint_checks.json').read_text())
unnorm=json.loads((P/'unnormalized_checks.json').read_text())
assert len(producer)==30 and len(audit['numerics'])==30
assert len(endpoint)==30 and len(unnorm)==30
assert {r['delta'] for r in producer}=={'0.0','0.5'}
assert {r['delta'] for r in audit['numerics']}=={'0.0','0.5'}
for r in producer:
    if r['n']>=300:assert abs(Decimal(r['relative_n4_error']))<Decimal('1e-8')
for r in audit['numerics']:
    assert Decimal(r['exact_tail_upper_bound'])<Decimal('1e-75')
    if r['n']>=400:assert abs(Decimal(r['relative_refined_error']))<Decimal('1e-8')
assert audit['audited_tex_sha256']==hashlib.sha256((P/'mahonian_crossover.tex').read_bytes()).hexdigest()
result={'status':'passed','producer_critical_cases':len(producer),'independent_critical_cases':len(audit['numerics']),'endpoint_cases':len(endpoint),'unnormalized_cases':len(unnorm),'producer_max_n':max(r['n'] for r in producer),'independent_max_n':max(r['n'] for r in audit['numerics']),'independent_tail_bound':'< 1e-75','tex_sha256':audit['audited_tex_sha256'],'scope':'Numerical regression, exact symbolic assertions in audit_independent.py, and audit hash consistency. Analytic remainders are established in the report.'}
(P/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
