#!/usr/bin/env python3
"""Independent, non-kernel byte-to-certificate binding audit."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
EXPECTED='6d30d89253629525b0af3066c7fec67b052c07413938fc7a94dd96ab1ff406e2'
def require(test,reason):
    if not test:raise SystemExit(reason)
raw=(ROOT/'normalized_certificate.json').read_bytes()
require(hashlib.sha256(raw).hexdigest()==EXPECTED,'Shared normalized JSON changed')
doc=json.loads(raw)
actual=[tuple(map(int,row)) for row in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',(ROOT/'NormalizedCert215.v').read_text())]
require(len(actual)==len(doc['entries'])==1426,'Wrong entry count')
def rocq_bits(n):
    ans=[]
    while n!=1:
        require(n>1,'Invalid positive path')
        ans.append(n&1);n//=2
    return ans
for i,((a,b,j,k),(c,d,l,m)) in enumerate(zip(actual,doc['entries'])):
    require(rocq_bits(a)==[int(x) for x in bin(int(c))[3:]],f'Left path {i} differs')
    require(rocq_bits(b)==[int(x) for x in bin(int(d))[3:]],f'Right path {i} differs')
    require((j,k)==(l,m),f'Successors {i} differ')
print(json.dumps({'result':'PASS_EXACT_SHARED_JSON_BINDING','entries':len(actual),'shared_json_sha256':EXPECTED,'scope':'Independent data binding audit, not a kernel proof'},indent=2))
