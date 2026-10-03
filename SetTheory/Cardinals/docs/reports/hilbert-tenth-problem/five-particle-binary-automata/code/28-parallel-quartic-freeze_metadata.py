"""Freeze portable research metadata after successful normal/optimized checks."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
normal=json.loads((R/'receipt.json').read_text());optimized=json.loads((R/'receipt-optimized.json').read_text())
if normal['status']!='PASS'or normal['counts']!=optimized['counts']or normal['ledgers']!=optimized['ledgers']:raise RuntimeError('baseline normal/optimized mismatch')
out={'source':'example-source.json','scope':'Fixed source m=2,p=1,a=0,J=0; whole forward horizon T=1; concrete emitted costs, not an improvement claim over prior certificates.','examples':{}}
for n in(0,1,2,3,5):
 v=normal['ledgers'][f'increment_right_n{n}_T1_inverseFalse'];out['examples'][str(n)]=dict(v,total_polynomial_variables=4*n+v['circuit']['witnesses'])
out['expanded_pair_quartic']=normal['ledgers']['expanded_pair_quartic'];out['serialized_pair_sos']=normal['ledgers']['serialized_pair_sos'];out['exact_formulas']={'witnesses':'W=2A+2I+G','residuals':'M=W+Q','checks':'Q=5n-2 for n>=1; Q=0 at n=0','horizon':'W(T)=4 max(n-1,0)+T(w_E+w_P)','per_block_bound':'O(K log^2(K+1)+nK(n+(J+2)^2+1)+n^3)','A_caveat':'A counts signed assignment registers, not bounded-fan-in additions; charge residual monomial occurrences and coefficient bits.'}
(R/'resource-ledger.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
files={}
for p in sorted(R.rglob('*')):
 if not p.is_file()or'__pycache__'in p.parts:continue
 name=p.relative_to(R).as_posix()
 if name in ('MANIFEST.json','SHA256SUMS','bundle-verification.json','bundle-verification-optimized.json'):continue
 b=p.read_bytes();files[name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
m={'schema':'parallel-quartic-research-manifest-v1','date':'2026-10-03','files':files}
(R/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
(R/'SHA256SUMS').write_text(''.join(record['sha256']+'  '+name+'\n'for name,record in files.items()))
print(json.dumps({'files':len(files),'bytes':sum(v['bytes']for v in files.values()),'manifest_sha256':hashlib.sha256((R/'MANIFEST.json').read_bytes()).hexdigest()},sort_keys=True))
