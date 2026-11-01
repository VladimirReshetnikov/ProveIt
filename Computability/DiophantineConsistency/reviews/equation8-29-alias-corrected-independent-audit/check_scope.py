#!/usr/bin/env python3
"""Check revised disclosure, historical model-replay receipt, and aliases."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;ROOT=D.parents[1];T=ROOT/'equation8-29.tex';C=ROOT/'research/adaptive-square-sums29-degree8/candidate.json';P=ROOT/'reviews/adaptive-aq29-model-replay';R=P/'receipt.json';O=P/'terminal-observation.json';F=ROOT/'reviews/adaptive-aq29-native-replay/terminal-observation.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inputs=[Path(__file__).resolve(),T,C,R,O,F];before={str(p):H(p) for p in inputs};t=T.read_text();c=json.loads(C.read_text());r=json.loads(R.read_text());o=json.loads(O.read_text());f=json.loads(F.read_text())
assert re.search(r'This equation is a candidate:\s*its model witness transport has been checked,\s*but its native intuitionistic PRA equivalence has not passed the guarded replay\.',t)
assert 'Lean proves that the formalized equation' not in t
assert 'fSquareVariable' not in c['witnesses'] and ['f2','*','f','f'] in c['source']
assert r'gate \texttt{m} is $m=f^2$' in t and '26. WComputed = g27 - g28\\\\' in t
assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and r['runs'][0]['rows']==r['runs'][1]['rows'] and len(r['runs'][0]['rows'])==6
assert o['observed_exit_code']==0 and o['observed_stdout']=='MATCHED_PASS 6 rows' and o['receipt_sha256']==H(R)
for run in r['runs']:
 for row in run['rows']:
  source=P/run['label']/'src/DiophantineConsistency'/(row['module']+'.lean'); log=P/run['label']/'logs'/(row['module']+'.log')
  assert H(source)==row['source_sha256'] and H(log)==row['log_sha256'] and row['exit']==0
assert f['status']=='FAILED' and f['observed_exit_code']==1
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_REVISED_SCOPE_AND_ALIASES','input_sha256':before,'scope':'Checks wording against historical model receipt and failed native attempt; object dependencies no longer all present. Does not replay Lean or audit transitive provenance.'};p=D/'scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
