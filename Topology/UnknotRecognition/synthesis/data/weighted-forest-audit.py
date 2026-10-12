"""Fresh source-cut audit: queue compatibility, weighted choices and literal cuts."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_three_handle_reduction import _raw_costs, reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.seeds import sources


def digest(value):return hashlib.sha256(json.dumps(json_safe(value),sort_keys=True).encode()).hexdigest()


def main():
    pins=sources();counts=Counter();records=[]
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    oldpath=DATA/'moment-boundary-audit.json';old={r['id']:r for r in json.loads(oldpath.read_text())['cases']}
    for c in bank:
        raw,rows=c['triangulation'],c['coordinates'];ref=old[c['id']]
        q=normal_cut_handlebodies(raw,rows,record_certificate=True,top_forest='queue')
        w=normal_cut_handlebodies(raw,rows,record_certificate=True)
        assert q['status']==ref['status']
        record=dict(id=c['id'],queue_status=q['status'],weighted_status=w['status'],reason=w.get('reason'))
        if q['status']=='COMPLETE':
            assert digest(q['certificate'])==ref['masks_sha256']
            assert verify_normal_cut_handlebodies(raw,rows,q['certificate'])
            assert w['status']=='COMPLETE' and q['census']==w['census']
            counts['queue_certificates_unchanged']+=1
        counts[w['status']]+=1
        if w['status']=='COMPLETE':
            assert verify_normal_cut_handlebodies(raw,rows,w['certificate'])
            record.update(histogram=w['census']['histogram'],certificate_sha256=digest(w['certificate']))
            if q['status']=='COMPLETE' and w['certificate']==q['certificate']:counts['weighted_certificates_unchanged']+=1
            if q['status']!='COMPLETE':counts['new_complete']+=1
        if 'interior' in c['id'] or c['id'].startswith('nested_'):
            p=_prepare(raw,lambda:None);g=_parallelity_geometry(p,_coordinates(p,rows,lambda:None),lambda:None)
            costs=_raw_costs(g['core'],lambda:None)
            costs_by_mode={}
            for mode in ('queue','max_weight'):
                reduced,proof=reduce_core_three_handles(g,strategy=mode)
                assert reduced==replay_core_three_handles(g,proof)
                costs_by_mode[mode]=sum(costs[h] for h in proof['surviving_two_handles'])
            assert costs_by_mode['max_weight']<=costs_by_mode['queue']
            record.update(retained_passages=costs_by_mode,source_three_handles=len(g['core']['handles3']))
            counts['lower_retained_cost']+=costs_by_mode['max_weight']<costs_by_mode['queue']
            m=normal_cut_handlebodies(raw,rows,record_certificate=True,boundary_method='moments')
            assert m['status']==w['status']
            if m['status']=='COMPLETE':
                assert m['census']==w['census']
                assert verify_normal_cut_handlebodies(raw,rows,m['certificate']);counts['moment_replays']+=1
        try:
            proc=subprocess.run([sys.executable,'-m','marked_parallelity_research.audit_census','--oracle'],
                                input=json.dumps(c),text=True,capture_output=True,cwd=ROOT/'fast',timeout=30)
            assert proc.returncode==0,proc.stderr
            literal=json.loads(proc.stdout);record['regina']=literal
            if 'histogram' in literal:
                counts['literal_cuts']+=1
                if w['status']=='COMPLETE':
                    assert w['census']['histogram']==literal['histogram'];counts['literal_agreements']+=1
            else:counts['literal_expansion_cap']+=1
        except subprocess.TimeoutExpired:
            record['regina']=dict(status='TIMEOUT',seconds=30);counts['literal_timeouts']+=1
        records.append(record)
        if len(records)%10==0:print(len(records),dict(counts),flush=True)
    assert pins==sources()
    assert counts['queue_certificates_unchanged']==102 and counts['COMPLETE']==104 and counts['new_complete']==2
    report=dict(native_source_sha256=pins,corpus_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                reference_sha256=hashlib.sha256(oldpath.read_bytes()).hexdigest(),
                counts=dict(counts),cases=records,oracle_scope='Fresh independent Regina source conversion, actual cutting and component recognition')
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
    print(dict(counts),flush=True)


if __name__=='__main__':main()
