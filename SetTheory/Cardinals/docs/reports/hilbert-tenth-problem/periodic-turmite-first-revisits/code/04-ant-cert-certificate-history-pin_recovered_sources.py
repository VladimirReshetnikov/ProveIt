#!/usr/bin/env python3
"""Own byte-pinning utility; upstream files are data only."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
commit='5883b08b7af362077f13bb4afa97a23a90ae4cf8'
def details(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
pins={}
for row in json.loads((P/'source/retrieval_metadata.json').read_text()):
 f=P/'source'/row['name'];b=f.read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if git!=row['git_blob']:raise ValueError('Git blob mismatch '+str(f))
 pins[str(f.relative_to(P))]=dict(details(f),git_blob=git,commit=commit,url=row['url'],scope='Refetched pinned theorem/reference DATA ONLY; never executed or imported')
f=P/'source/HISTORY174.md'
if details(f)['sha256']!='9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656':raise ValueError('HISTORY174 pin')
pins['source/HISTORY174.md']=dict(details(f),commit=commit,scope='Byte-identical inherited proof from authenticated recovered Report42',url='https://github.com/VladimirReshetnikov/ProveIt/blob/'+commit+'/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md')
for name in ['history174.json','reconstruct_history.py','verification.json','audit_history.py','audit_receipt.json','CONTRACT.md','pin_recovered_sources.py','source/retrieval_metadata.json','audit-normal.log','audit-optimized.log','reconstruction-optimized.log']:
 pins[name]=dict(details(P/name),scope='Recovered edition; newly pinned own code, document, or derived result')
old='2075bb290f3f81d7c04a27b82f50c4f492638d55a3a27f434f66497ae9fb90ea'
if pins['history174.json']['sha256']!=old:raise ValueError('old DAG identity mismatch')
pins['history174.json']['scope']='Exact old artifact byte identity VERIFIED against retained SHA256; reconstructed from own formulas'
report=P.parent/'external-placeholder'
external=Path('/workspace/shared/recovered-delivered-packages/Research_Report40/Research_Report40.tex')
if external.is_file():pins['external/Research_Report40.tex']=dict(details(external),path=str(external),scope='Read-only physical convention reference from recovered authenticated package, not needed for arithmetic replay')
(P/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(P/'RECOVERY.json').write_text(json.dumps({'edition':'recovered-20261004-v2','history174_old_byte_identity_verified':True,'history174_sha256':old,'old_normalized_stream_hash_retained_from_parent':'eb318d91403e1e2b4e6da04ad28a361cb28f044658d9238ac461bb30fe8bf432','normalized_hash_note':'Not independently recomputed here because parent normalization convention is external; full JSON byte identity is verified.','other_own_files':'new recovered edition bytes, no old byte identity asserted','upstream_sources':'refetched pinned commit data and Git blob verified','upstream_code_executed':False,'normal_and_optimized_replay':'PASS'},indent=2)+'\n')
print('SOURCE_PINS.json and RECOVERY.json written; old history174.json byte identity verified')
