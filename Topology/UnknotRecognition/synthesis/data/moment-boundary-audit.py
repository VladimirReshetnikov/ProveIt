"""Complete cut differential audit with retained independent Regina references."""
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.parallelity_boundary_moments import native_projection
from normal_orbit_research.seeds import sources


def main():
    pins=sources()
    corpus=ROOT/'fast/marked_parallelity_research/corpus.json'
    extra=ROOT/'fast/marked_parallelity_research/three_handle_corpus.json'
    bank=json.loads(corpus.read_text())['cases'];additional=json.loads(extra.read_text())['cases']
    historical=json.loads((DATA/'three-handles-audit.json').read_text())
    extra_reference=json.loads((DATA/'three-handles-source-audit.json').read_text())
    assert historical['corpus_sha256']==hashlib.sha256(corpus.read_bytes()).hexdigest()
    assert extra_reference['fixture_sha256']==hashlib.sha256(extra.read_bytes()).hexdigest()
    old={r['id']:r for r in historical['cases']};other={r['id']:r for r in extra_reference['cases']}
    records=[]
    for c in bank+additional:
        raw,rows=c['triangulation'],c['coordinates']
        a=normal_cut_handlebodies(raw,rows,boundary_method='masks',record_certificate=True)
        b=normal_cut_handlebodies(raw,rows,boundary_method='moments',record_certificate=True)
        ref=old.get(c['id'],other.get(c['id']))
        assert a['status']==b['status']==ref.get('native_status',ref.get('status'))
        r=dict(id=c['id'],status=b['status'],mask_reason=a.get('reason'),moment_reason=b.get('reason'),
               inherited_case=c['id'] in old)
        if a['status']=='COMPLETE':
            assert a['census']==b['census']
            assert a['certificate']['boundary']['skeleton']==native_projection(b['certificate']['boundary']['skeleton'])
            assert verify_normal_cut_handlebodies(raw,rows,a['certificate'])
            assert verify_normal_cut_handlebodies(raw,rows,b['certificate'])
            before=json.dumps(json_safe(a['certificate']),sort_keys=True).encode()
            if c['id'] in old:assert hashlib.sha256(before).hexdigest()==ref['certificate_sha256']
            if 'histogram' in ref['regina']:assert b['census']['histogram']==ref['regina']['histogram']
            after=json.dumps(json_safe(b['certificate']),sort_keys=True).encode()
            r.update(schema=b['certificate']['schema'],histogram=b['census']['histogram'],
                     masks_sha256=hashlib.sha256(before).hexdigest(),moments_sha256=hashlib.sha256(after).hexdigest(),
                     masks_bytes=len(before),moments_bytes=len(after),
                     literal_reference='histogram' in ref['regina'])
        records.append(r)
        if len(records)%10==0:print(len(records),flush=True)
    assert sources()==pins
    report=dict(native_source_sha256=pins,corpus_sha256=hashlib.sha256(corpus.read_bytes()).hexdigest(),
                fixture_sha256=hashlib.sha256(extra.read_bytes()).hexdigest(),cases=records,
                oracle_scope='Retained literal Regina references on identical source files; no oracle rerun',
                reference_sha256={n:hashlib.sha256((DATA/n).read_bytes()).hexdigest() for n in
                                  ('three-handles-audit.json','three-handles-source-audit.json')},
                complete=sum(r['status']=='COMPLETE' for r in records),
                earlier_masks_unchanged=sum(r['status']=='COMPLETE' and r['inherited_case'] for r in records),
                literal_agreements=sum(r.get('literal_reference',False) for r in records))
    assert report['complete']==102 and report['earlier_masks_unchanged']==92 and report['literal_agreements']==95
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
    print({k:v for k,v in report.items() if k not in ('cases','native_source_sha256','reference_sha256')})


if __name__=='__main__':main()
