#!/usr/bin/env python3
"""SOURCE DATA ONLY: derive candidate sorted-tile index witness for Lean K bridge."""
import hashlib,importlib.util,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;cert=here.parent/'padding-staircase-independent/certify.py';coeff=here.parent/'padding-staircase-independent/coefficients.json';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(cert.read_bytes())=='56b3865237699c486bbd940a88e94387d26092ac2cf89cd7f9097206dd8fb975';assert sha(coeff.read_bytes())=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
spec=importlib.util.spec_from_file_location('padding_certificate',cert);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);_,_,_,tiles,calibrated,_=module.model();values=json.loads(coeff.read_bytes());assert calibrated==values and len(tiles)==942
# External transcription of MFWangTiles942Permutation.recoveredIndex. It must
# be proved against the actual Lean definitions, not treated as that proof.
def index(t):
 w,n,e,s=t
 if 2<=n<=431:return n-1
 if s==438:return 923+2*(n//432)+n%432
 if n<=1:return 433+n if s==n else 423+2*(w+e)+n
 if n<=433:return n-1
 if n==434:return 927
 if n==435:return 0
 if n==436:return 928 if s==4 else 929
 if n==437:return 933+3*(2 if w==4 else w)+e
 return 496+s
def weight(t):
 w,n,e,s=t
 return 1+2**10*(1+w+2**8*n+2**17*e+2**25*s)
rows=[{'physical':p,'index':index(t),'tile':list(t),'weight':weight(t)} for p,t in enumerate(tiles)]
assert rows[0]['index']==0 and sorted(x['index'] for x in rows)==list(range(942))
assert all(2*x['weight']==values[x['physical']] for x in rows)
assert all(rows[i]['weight']>rows[i+1]['weight'] for i in range(1,941))
result={'status':'EXTERNAL_CANDIDATE_ONLY','count':len(rows),'start_index':0,
 'certificate_sha256':sha(cert.read_bytes()),'coefficient_array_sha256':sha(coeff.read_bytes()),
 'rows':rows,'scope':'Untrusted external witness; Lean tile/rank/port/file equalities not proved.'}
out=here/'witness.json'
if out.exists():raise SystemExit('refusing overwrite')
encoded=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode();out.write_bytes(encoded)
print(json.dumps({'status':'GENERATED_SOURCE_DATA_ONLY','count':len(rows),'witness_sha256':sha(encoded),
 'scope':'External finite candidate only; no Lean theorem.'},indent=2,sort_keys=True))
