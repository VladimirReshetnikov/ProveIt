"""Expand the contextual example's exact sum-of-squares polynomial."""
from motif_compiler import Poly
from pathlib import Path
import json
ROOT=Path(__file__).parent
source=json.loads((ROOT/'contextual_copy_polynomials.json').read_text())
residuals=[Poly({tuple(m):c for c,m in terms}) for terms in source['residuals'].values()]
sos=sum((p*p for p in residuals),Poly())
assert sos.degree<=4 and sos.evaluate(source['witness'])==0
assert all(p.evaluate(source['witness'])==0 for p in residuals)
# A one-coordinate change must make the SOS a strictly positive integer.
w=source['witness'].copy(); name=next(n for n in source['variables'] if n.startswith('u:'))
w[name]+=1
assert sos.evaluate(w)==sum(p.evaluate(w)**2 for p in residuals)>0
out={'convention':'Exact expansion of the sum of squared residuals from contextual_copy_polynomials.json; natural variables; terms are [integer coefficient, sorted variable-name monomial].','variables':source['variables'],'degree':sos.degree,'monomial_count':len(sos.t),'terms':sos.as_json(),'witness':source['witness']}
(ROOT/'contextual_copy_quartic.json').write_text(json.dumps(out,indent=2)+'\n')
receipt={'status':'passed','residuals':len(residuals),'degree':sos.degree,'monomial_count':len(sos.t),'coefficient_height':max(abs(c)for c in sos.t.values()),'witness_value':0,'mutated_value':sos.evaluate(w)}
(ROOT/'quartic_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
