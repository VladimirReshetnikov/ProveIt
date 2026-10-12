"""Exercise the v5 kernel directly, including inputs preferring older schemas.

Uses existing source-bound orbit certificates and independent whole-cut replay.
Oracle histograms come from the current source-pinned literal-cut audit.
"""
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.bundle_boundary_kernel import bundle_boundary_kernel
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources
pins=sources()
audit=json.loads((ROOT/'synthesis/data/boundary-kernel-audit.json').read_text())
assert audit['native_source_sha256']==pins
reference={c['id']:c for c in audit['cases']}
bank=json.loads((ROOT/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
records=[]
for c in bank:
    p=normal_cut_parallelity(c['triangulation'],c['coordinates'],record_certificate=True)
    if p['geometry']['core']['handles3']:continue
    b=normal_parallelity_boundary_words(c['triangulation'],c['coordinates'],record_certificate=True)
    k=bundle_boundary_kernel(p['geometry'],p['summary'],b['skeleton'])
    row=dict(id=c['id'],certified=k is not None,preferred_status=reference[c['id']]['native_status'])
    if k is not None:
        proof,census,stats=k
        cert=dict(schema='normal-cut-handlebodies-v5',parallelity=p['certificate'],boundary=b['certificate'],kernel=proof,census=census)
        assert verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],cert)
        oracle=reference[c['id']]['regina'].get('histogram')
        if oracle is not None:assert census['histogram']==oracle
        row.update(census=census['histogram'],literal_oracle_agreement=oracle is not None,
                   certificate_sha256=hashlib.sha256(json.dumps(json_safe(cert),sort_keys=True).encode()).hexdigest())
    records.append(row)
    if len(records)%10==0:print(len(records),sum(r['certified'] for r in records),flush=True)
assert pins==sources()
report=dict(scope='Direct v5 source certificate audit; preferred older certificates unchanged',native_source_sha256=pins,
            source_audit_sha256=hashlib.sha256((ROOT/'synthesis/data/boundary-kernel-audit.json').read_bytes()).hexdigest(),
            cases=records,certified=sum(r['certified'] for r in records),literal_oracle_agreements=sum(r.get('literal_oracle_agreement',False) for r in records))
Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
print('certified',report['certified'],'literal',report['literal_oracle_agreements'],flush=True)
