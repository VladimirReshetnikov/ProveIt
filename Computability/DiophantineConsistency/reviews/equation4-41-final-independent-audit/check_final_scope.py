#!/usr/bin/env python3
"""Check final presentation wording against the exact native endpoint receipt."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;ROOT=D.parents[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();tex=ROOT/'equation4-41.tex';native=ROOT/'Lean/DiophantineConsistency/IPRAQF41Native.lean';check=ROOT/'Lean/DiophantineConsistency/IPRAQF41NativeChecks.lean';rr=ROOT/'reviews/adaptive-qf41-native-replay/receipt.json';obs=rr.parent/'terminal-observation.json';logs=[rr.parent/x/'logs'/f'{name}.log' for x in ('author','peer') for name in ('IPRAQF41Native','IPRAQF41NativeChecks')];inputs=[Path(__file__).resolve(),tex,native,check,rr,obs,*logs];before={str(p):H(p) for p in inputs};t=' '.join(tex.read_text().split());n=' '.join(native.read_text().split());r=json.loads(rr.read_text());o=json.loads(obs.read_text())
assert 'This equation is a candidate' not in t
for x in ['Lean proves that the formalized equation has no positive solution exactly','the specified intuitionistic PRA.','replayed on a fixed source snapshot; some transitive dependencies remain inherited.']:assert x in t
for x in ['theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero','positiveShift (AdaptiveQF41Context.literal CurrentWindowCarry2011.ports)','∼mappedNativeRefutation embedding','equivalence_of_bridge literalNatural bridge41']:assert x in n
assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and o['observed_exit_code']==0 and o['receipt_sha256']==H(rr)
for name,path in [('IPRAQF41Native',native),('IPRAQF41NativeChecks',check)]:
 rows=[next(x for x in run['rows'] if x['module']==name) for run in r['runs']]
 for x,run in zip(rows,r['runs']):assert x['exit']==0 and x['source_sha256']==H(path) and x['log_sha256']==H(rr.parent/run['label']/'logs'/f'{name}.log')
 for k in ('source_sha256','object_sha256','log_sha256'):assert rows[0][k]==rows[1][k]
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_SCOPE_AND_ENDPOINT_RECEIPT','input_sha256':before,'checked_endpoint':'nativeTheory proves shifted fixed-port literal no-zero iff negated mapped native ZFC refutation','proof_scope':'Checks wording and matching endpoint source/log receipt rows; interpretation of the arithmetized statement and inherited project-transitive, package-transitive and dynamic ancestry are not independently replayed here.'};p=D/'scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
