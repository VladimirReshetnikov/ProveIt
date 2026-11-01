#!/usr/bin/env python3
"""Check final presentation wording against the exact native endpoint receipt."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent; ROOT=D.parents[1]; H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tex=ROOT/'equation4-42.tex'; native=ROOT/'Lean/DiophantineConsistency/IPRAQV42Native.lean'; rr=ROOT/'reviews/adaptive-qv42-native-final-replay/receipt.json'; obs=rr.parent/'terminal-observation.json'; logs=[rr.parent/x/'logs/IPRAQV42Native.log' for x in ('author','peer')]; inputs=[Path(__file__).resolve(),tex,native,rr,obs,*logs];before={str(p):H(p) for p in inputs};t=' '.join(tex.read_text().split());n=' '.join(native.read_text().split());r=json.loads(rr.read_text());o=json.loads(obs.read_text())
assert 'This equation is a candidate' not in t
for x in ['Lean proves that the formalized equation has no positive solution exactly','the specified intuitionistic PRA.','replayed on a fixed source snapshot; some transitive dependencies remain inherited.']:assert x in t
for x in ['theorem literal_equivalence : IPRANativeTheory.nativeTheory ⊢ IPRAExpressionNative.nativeNoZero','positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports)','∼IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding','conditional_native AdaptiveVSignMachine43.machineOrients']:assert x in n
assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and o['observed_exit_code']==0 and o['receipt_sha256']==H(rr)
rows=[next(x for x in run['rows'] if x['module']=='IPRAQV42Native') for run in r['runs']]
assert all(x['exit']==0 and x['source_sha256']==H(native) and x['log_sha256']==H(log) for x,log in zip(rows,logs))
for k in ('source_sha256','object_sha256','log_sha256'):assert rows[0][k]==rows[1][k]
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_SCOPE_AND_ENDPOINT_RECEIPT','input_sha256':before,'checked_endpoint':'nativeTheory proves shifted fixed-port literal no-zero iff negated mapped native ZFC refutation','proof_scope':'Checks wording and matching endpoint source/log receipt rows; interpretation of the arithmetized statement and inherited project-transitive, package-transitive and dynamic ancestry are not independently replayed here.'};p=D/'scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
