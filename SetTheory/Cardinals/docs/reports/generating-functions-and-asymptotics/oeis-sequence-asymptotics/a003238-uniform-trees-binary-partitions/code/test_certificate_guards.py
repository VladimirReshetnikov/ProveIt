"""Deliberately corrupt receipt compatibility and contradiction data.
Run once normally and once with python -O. A failure to reject aborts the test.
"""
from pathlib import Path
from copy import deepcopy
import json,sys
from combine_certificate import combine_receipts
P=Path(__file__).resolve().parent
r=json.loads((P/'RADIAL_VALUE_CERTIFICATE.json').read_text())
o=json.loads((P/'OPERATOR_VALUE_CERTIFICATE.json').read_text())
valid_rows,valid_gap=combine_receipts(r,o)
if valid_gap.lo<=0:raise RuntimeError('genuine certificate unexpectedly fails')
tests=[]
def reject(name,rr,oo,expected):
 try:combine_receipts(rr,oo)
 except ValueError as e:
  if expected not in str(e):raise RuntimeError((name,'unexpected failure',str(e)))
  tests.append({'case':name,'rejected':True,'reason':str(e)});return
 raise RuntimeError(('UNSAFE: poisoned receipt accepted',name))
rr=deepcopy(r);rr['precision_bits']=128;reject('precision mismatch',rr,o,'precision mismatch')
rr=deepcopy(r);rr['rows']=rr['rows'][:1];reject('wrong row count',rr,o,'exactly two')
rr=deepcopy(r);rr['rows'][0]['t']='1/8';reject('different points',rr,o,'test point mismatch')
oo=deepcopy(o);oo['rows'][0]['S3_integer_bounds'][0]='0';reject('S3 touches zero',r,oo,'positive S3')
oo=deepcopy(o);oo['rows'][0]['14T4_integer_bounds'][0]='-1';reject('negative remainder',r,oo,'nonnegative remainder')
rr=deepcopy(r);rr['rows'][0]['H_integer_bounds'].reverse();reject('reversed endpoints',rr,o,'reversed interval')
rr=deepcopy(r);oo=deepcopy(o);rr['rows'][1]=deepcopy(rr['rows'][0]);oo['rows'][1]=deepcopy(oo['rows'][0]);reject('overlapping conditional constant intervals',rr,oo,'intervals overlap')
rr=deepcopy(r);oo=deepcopy(o);rr['rows'].reverse();oo['rows'].reverse();reject('wrong interval order',rr,oo,'wrong order')
rr=deepcopy(r);rr['status']='NOT_CERTIFIED';reject('wrong receipt status',rr,o,'unexpected radial')
receipt={'status':'PASS','valid_receipt_accepted':True,'deliberate_failures':tests}
print(json.dumps(receipt,indent=2))
