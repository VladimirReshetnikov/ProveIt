"""Check the reference run's complete source and cross-manifest provenance."""
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
production=json.loads((r/'production_manifest.json').read_text())
independent=json.loads((r/'independent_manifest.json').read_text())
coverage=json.loads((r/'independent_coverage.json').read_text())
numeric=json.loads((r/'independent_numeric_index.json').read_text())
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(r/'producer_v1.cpp')==production['source_sha256']==independent['producer_source_sha256']
assert digest(r/'audit_residual_enclosures.cpp')==independent['independent_verifier_source_sha256']
assert digest(r/'independent_manifest.json')==coverage['manifest_sha256']
assert [c['m']for c in production['cases']]==[c['m']for c in independent['cases']]==[c['m']for c in numeric['cases']]==list(range(2,112))
for p,a,n in zip(production['cases'],independent['cases'],numeric['cases']):
    assert p['pressure_sha256']==a['production_pressure_sha256']
    assert p['trace_sha256']==a['production_trace_sha256']
    assert a['fresh_radii_sha256']==n['fresh_radii_sha256']
    assert a['all_fresh_lower_endpoints_positive']
    assert a['positive_pressure_degrees']==2*p['m']-1
    assert a['positive_order_response_states']==6*p['m']-2
assert coverage['complete'] and coverage['all_hash_links_match']
assert coverage['positive_pressure_coefficients']==12320 and coverage['positive_order_response_states']==37070
versions=json.loads((r/'producer_versions.json').read_text())
assert digest(r/'producer_v1.cpp')==versions['original_producer_sha256']
assert digest(r/'produce_guarded.cpp')==versions['guarded_replayer_sha256']
print('PASS: all source hashes, 110-case manifests and production-to-independent links.')
