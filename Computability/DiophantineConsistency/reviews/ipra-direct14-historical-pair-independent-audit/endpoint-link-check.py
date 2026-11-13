#!/usr/bin/env python3
"""Bind the direct14 paired source to the separately audited author endpoint."""
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];RUN=Path('/tmp/ipra-direct14-historical-paired-run-01');AUTHOR=BASE/'reviews/ipra-standard-direct14-guarded-author';AUDIT=BASE/'reviews/ipra-standard-direct14-guarded-author-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
manifest=J(RUN/'snapshot/manifest.json');name='DiophantineConsistency.IPRAStandardDirect14';source=RUN/'snapshot'/manifest['sources'][name]['snapshot_path'];state=J(AUTHOR/'state.json');row=next(r for r in state['rows'] if r['module']==name);prior=J(AUDIT/'receipt.json');terminal=J(AUDIT/'terminal-observation.json')
assert prior['status']=='PASS_INDEPENDENT_DIRECT14_AUTHOR_ARTIFACT_AUDIT' and terminal['observed_exit_code']==0 and terminal['receipt_sha256']==H(AUDIT/'receipt.json')
assert prior['trial_state_sha256']==H(AUTHOR/'state.json') and H(source)==row['source_sha256']==manifest['sources'][name]['sha256']
s=source.read_text();assert ('theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero\n    (positiveShift (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)) 🡘\n      ∼mappedNativeRefutation embedding :=') in s
assert ('theorem literal_iff_translated_consistency : standardTheory ⊢\n    IPRAExpressionNative.nativeNoZero\n      (positiveShift (AdaptiveSquareWitnessDirect14.literal CurrentWindowCarry2011.ports)) 🡘\n        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=') in s
files=[Path(__file__),source,RUN/'snapshot/manifest.json',AUTHOR/'state.json',AUDIT/'receipt.json',AUDIT/'terminal-observation.json'];before={str(p.resolve()):H(p) for p in files}
assert {str(p.resolve()):H(p) for p in files}==before
result={'status':'PASS_DIRECT14_PAIRED_ENDPOINT_SOURCE_LINK','inputs_sha256':before,'scope':'Finite source link to historical author audit; no Lean replay or PDF semantics.'};out=HERE/'endpoint-link-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
