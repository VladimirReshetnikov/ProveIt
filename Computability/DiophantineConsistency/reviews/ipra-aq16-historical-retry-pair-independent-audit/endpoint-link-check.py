#!/usr/bin/env python3
"""Bind all AQ16 retry sources to the separately audited author and port proof."""
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];RUN=Path('/tmp/ipra-aq16-historical-paired-run-02');AUTHOR=BASE/'reviews/ipra-aq16-guarded-author';AUDIT=BASE/'reviews/ipra-aq16-guarded-author-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
manifest=J(RUN/'snapshot/manifest.json');state=J(AUTHOR/'state.json');prior=J(AUDIT/'receipt.json');terminal=J(AUDIT/'terminal-observation.json')
assert prior['status']=='PASS_INDEPENDENT_AQ16_AUTHOR_ARTIFACT_AUDIT' and terminal['observed_exit_code']==0 and terminal['receipt_sha256']==H(AUDIT/'receipt.json')
assert prior['trial_state_sha256']==H(AUTHOR/'state.json')
names=[r['module'] for r in state['rows']];assert len(names)==52 and names==manifest['order'][1210:]
sources=[]
for row in state['rows']:
 name=row['module'];source=RUN/'snapshot'/manifest['sources'][name]['snapshot_path']
 assert H(source)==row['source_sha256']==manifest['sources'][name]['sha256'];sources.append(source)
endpoint=(RUN/'snapshot'/manifest['sources']['DiophantineConsistency.IPRAStandardAQ16']['snapshot_path']).read_text()
port=(RUN/'snapshot'/manifest['sources']['DiophantineConsistency.AdaptiveAQ16']['snapshot_path']).read_text()
assert 'theorem literal_iff_translated_consistency : standardTheory ⊢' in endpoint and 'AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports' in endpoint
assert '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ' in endpoint
assert '(p : Fin 4 → ℕ) (hp : 2 ≤ p 0)' in port and '2 ≤ CurrentMasks2011.beta' in port and 'ArithmeticAdaptiveScaledNorms2011.currentPorts_cast' in port
files=[Path(__file__),*sources,RUN/'snapshot/manifest.json',AUTHOR/'state.json',AUDIT/'receipt.json',AUDIT/'terminal-observation.json'];before={str(p.resolve()):H(p) for p in files};assert before=={str(p.resolve()):H(p) for p in files}
result={'status':'PASS_AQ16_RETRY_PAIRED_ENDPOINT_SOURCE_LINK','inputs_sha256':before,'scope':'Finite source link and fixed-port condition only; no Lean replay or PDF semantics.'};out=HERE/'endpoint-link-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
