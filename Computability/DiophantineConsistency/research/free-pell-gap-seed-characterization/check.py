#!/usr/bin/env python3
"""Source and finite nonresidue controls for an ordinary existence theorem."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);r={row[0]:row for row in g['source']}
assert r['N0']==['N0','-','tau2','first_product'] and r['N1']==['N1','-','main_square','Dc2']
assert r['Nt']==['Nt','-','transport_partial','zqm'] and r['scaled_Ns']==['scaled_Ns','-','scaled_f2','normalized_S2']
assert r['product0']==['product0','*','N0','N1'] and r['product1']==['product1','*','product0','Na']
assert r['product3']==['product3','*','product1','Nt'] and r['product4']==['product4','*','product3','scaled_Ns']
for S in range(2,65):
 d=S*S-1
 assert all((v*v+1)%d!=0 for v in range(d))
 if S%2: assert d%8==0
 else:
  assert d%4==3
  assert any(d%p0==0 and p0%4==3 and all(p0%a for a in range(2,math.isqrt(p0)+1)) for p0 in range(3,d+1,4))
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'nonresidue_S_values':63,'scope':'finite controls for an ordinary unbounded theorem; no actual-port seed, Lean or full zero'},sort_keys=True,indent=2))
