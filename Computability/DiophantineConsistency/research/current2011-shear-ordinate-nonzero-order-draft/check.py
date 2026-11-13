#!/usr/bin/env python3
"""Read-only literal and bounded arithmetic checks; no Lean invocation."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-ordinate-nonzero-order-draft/ShearNonzero.lean.src':'c67931ea31c2fbedc6d0976f5d188fe9bf5633bfe4a51062a0c64e81dd1a66f3',
 'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
 'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
 'research/current2011-sheared72-46-proof-draft/ShearDraft.lean':'a479640aa326cb2190d530bb806d199f29c77796acd8f93edaffe609e5a8af2a',
}
for name,expected in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected: raise RuntimeError('pin changed: '+name)
g=json.loads((ROOT/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes()); rows={r[0]:r for r in g['source']}
expected=[['I','*','i','c2'],['Aaux','*','Delta','f2m1'],['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux'],['strong_residual','-','I2','Aaux']]
for row in expected:
 if rows.get(row[0])!=row: raise RuntimeError('literal cut mismatch: '+row[0])
if 'theorem auxiliary_shear' not in (ROOT/'research/current2011-sheared72-46-proof-draft/ShearDraft.lean').read_text(): raise RuntimeError('missing prior shear interface')
count=0
for A in range(0,20):
 for I in range(2,12):
  for y in range(1,8):
   V=-y; U=A*y*y; H=I*I-A; count+=1
   if U*U+H*H<4: raise RuntimeError('inequality diagnostic failed')
if (1*1+(1*1-1)**2)!=1: raise RuntimeError('I>=2 negative control failed')
print(json.dumps({'scope':'bounded integer controls and source pins; uncompiled generic lemma',
 'literal_rows_checked':len(expected),'bounded_cases':count,'I_bound_negative_control':True},indent=2,sort_keys=True))
