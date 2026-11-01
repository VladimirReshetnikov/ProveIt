#!/usr/bin/env python3
"""Check final presentation wording against the exact native endpoint receipt."""
from pathlib import Path
import hashlib, json
D=Path(__file__).resolve().parent; ROOT=D.parents[1]; H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tex=ROOT/'equation6-31.tex'; native=ROOT/'Lean/DiophantineConsistency/IPRAAQ31Native.lean'; check=ROOT/'Lean/DiophantineConsistency/IPRAAQ31NativeChecks.lean'; rr=ROOT/'reviews/adaptive-aq31-native-final-replay/receipt.json'; aa=rr.parent/'independent-audit.json'; obs=rr.parent/'terminal-observation.json'
inputs=[Path(__file__).resolve(),tex,native,check,rr,aa,obs]; before={str(p):H(p) for p in inputs}; t=' '.join(tex.read_text().split()); n=' '.join(native.read_text().split()); a=json.loads(aa.read_text()); r=json.loads(rr.read_text());
assert 'This equation is a candidate' not in t
for x in ['Lean proves that the formalized equation has no positive solution exactly','the specified intuitionistic PRA.','replayed on a fixed source snapshot; some transitive dependencies remain inherited.']: assert x in t
for x in ['theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero','positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports)','∼mappedNativeRefutation embedding','conditional_native machineOrients']: assert x in n
assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and a['status']=='PASS' and a['receipt_sha256']==H(rr)
for module,path in [('IPRAAQ31Native',native),('IPRAAQ31NativeChecks',check)]:
 rows=[next(x for x in run['rows'] if x['module']==module) for run in r['runs']]
 assert all(x['exit']==0 and x['source_sha256']==H(path) for x in rows)
 for k in ('source_sha256','object_sha256','log_sha256'): assert rows[0][k]==rows[1][k]
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_SCOPE_AND_ENDPOINT_RECEIPT','input_sha256':before,'checked_endpoint':'nativeTheory proves shifted fixed-port literal no-zero iff negated mapped native ZFC refutation','proof_scope':'Checks displayed wording and matched receipt against endpoint source; the separate interpretation of the arithmetized statement and transitive/dynamic ancestry are not independently replayed here.'}
p=D/'scope-receipt.json'; assert not p.exists(); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
