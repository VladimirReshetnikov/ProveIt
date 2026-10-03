"""Cross-check claims across regenerated receipts and exact exported coefficients."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
def read(p):return json.loads((ROOT/p).read_text())
f=read('replay/frontend-receipt.json');assert f['status']=='PASS' and f['clocks']==46 and f['symbolic_macrosteps']==58 and f['strict_minimum_inequalities']==43065
forms=read('replay/affine-gap-forms.json');assert len(forms)==64 and sum(x['multiplicity'] for x in forms)==43065
assert all(x['a']>=0 and x['b']>=0 and x['c']+x['a']*x['Q_min']+x['b']*x['Y_min']>=1 for x in forms)
ind=read('receipts/independent-receipt.json');assert ind['status']=='PASS' and ind['unbounded_symbolic_macros']==58
q=read('replay/grouped-quadratic7-certificate.json');assert (q['witness_count'],q['squared_linear_count'],q['product_count'],q['degree'])==(245,39,14,2)
e=read('replay/grouped-quadratic7-fixture.json');assert len(q['witnesses'])==245 and all(type(e[v]) is int and e[v]>=0 for v in q['witnesses'])
def at(poly):
 total=0
 for t in poly:
  z=t['coefficient']
  for v in t['monomial']:z*=e[v]
  total+=z
 return total
assert sum(at(r['polynomial'])**2 for r in q['squared_linear_residuals'])+sum(at(r['left'])*at(r['right']) for r in q['nonnegative_products'])==0
assert e['C']==189 and e['tau']==428
h=read('receipts/halting-example.json');assert h['prehalt_firings']==e['C'] and h['halt_timestamp']==e['tau']
qi=read('receipts/quadratic-independent.json');assert qi['symbolic_numeric_alignment_cases']==400 and qi['status']=='PASS'
c=read('replay/certificate-receipt.json');assert c['status']=='PASS' and c['natural_ledger']['total']==22 and c['positive_witness_ledger']['total']==26
out={'status':'PASS','matrix_entries':2116,'symbolic_macrosteps':58,'strict_minimum_inequalities':43065,'distinct_affine_forms':64,'quadratic_fixture':{'k':7,'witnesses':245,'linear_squares':39,'products':14,'degree':2,'C':189,'tau':428},'independent_coefficient_alignment_cases':400,'common_column_ledger_operations':22,'scope':'Exact finite-horizon universal-machine certificates; separate horizon-free decidable subclass.'}
(ROOT/'receipts/release-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
