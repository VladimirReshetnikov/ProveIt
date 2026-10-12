"""Compare all old/new cut queries and precheck modes, with source-bound replay."""
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'fast'),str(Path(__file__).parent/'column-baseline')]
from loader import load
from fastunknot.core_handlebody import _forest,_occurrences
from fastunknot.column_cancellation_verify import verify_raw_cancellation_obstruction
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.seeds import sources
baseline=load();old=baseline['normal_cut_handlebodies'].normal_cut_handlebodies
old_verify=baseline['normal_cut_handlebodies_verify'].verify_normal_cut_handlebodies
pins=sources();bank=json.loads((ROOT/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
historical=json.loads((ROOT/'synthesis/data/boundary-kernel-audit.json').read_text())
previous={c['id']:c for c in historical['cases']};records=[]
for c in bank:
    raw,rows=c['triangulation'],c['coordinates']
    before=old(raw,rows,record_certificate=True)
    after=normal_cut_handlebodies(raw,rows,record_certificate=True)
    nofilter=normal_cut_handlebodies(raw,rows,record_certificate=True,precheck_core=False)
    assert before['status']==after['status']==nofilter['status']==previous[c['id']]['native_status']
    row=dict(id=c['id'],status=after['status'],old_reason=before.get('reason'),new_reason=after.get('reason'),
             precheck_skipped_boundary='core_precheck' in after['stats'] and 'boundary' not in after['stats'])
    if before['status']=='COMPLETE':
        assert before['census']['histogram']==after['census']['histogram']==nofilter['census']['histogram']
        assert after['certificate']==nofilter['certificate']
        assert old_verify(raw,rows,before['certificate'])
        assert verify_normal_cut_handlebodies(raw,rows,before['certificate'])
        assert verify_normal_cut_handlebodies(raw,rows,after['certificate'])
        encoded=json.dumps(json_safe(before['certificate']),sort_keys=True).encode()
        assert hashlib.sha256(encoded).hexdigest()==previous[c['id']]['certificate_sha256']
        row.update(old_schema=before['certificate']['schema'],new_schema=after['certificate']['schema'],
                   certificate_unchanged=before['certificate']==after['certificate'])
    if row['precheck_skipped_boundary']:
        prepared=_prepare(raw,lambda:None);vector=_coordinates(prepared,rows,lambda:None)
        core=_parallelity_geometry(prepared,vector,lambda:None)['core']
        tree,_=_forest(core,lambda:None);counts=_occurrences(core,tree,lambda:None)
        from fastunknot.core_handlebody import column_cancellation_plan
        blocked=column_cancellation_plan(counts)['remaining_rows']
        assert verify_raw_cancellation_obstruction(counts,blocked)
        row['source_stopping_rows']=blocked
    records.append(row)
    if len(records)%10==0:print(len(records),flush=True)
assert sources()==pins
report=dict(native_source_sha256=pins,baseline_revision='5578c6e6629a5c63fc5b40ea14d1f49c9d5a8c8c',
            cases=records,complete=sum(c['status']=='COMPLETE' for c in records),
            skipped_boundaries=sum(c['precheck_skipped_boundary'] for c in records),
            unchanged_certificates=sum(c.get('certificate_unchanged',False) for c in records))
Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
print({k:v for k,v in report.items() if k not in ('native_source_sha256','cases')})
