"""Fresh source-cut audit for frozen lower forests and cached adaptive retry."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources


def digest(value):return hashlib.sha256(json.dumps(json_safe(value),sort_keys=True).encode()).hexdigest()


def main():
    pins=sources();counts=Counter();records=[]
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    oldpath=DATA/'weighted-forest-audit.json';old={r['id']:r for r in json.loads(oldpath.read_text())['cases']}
    for c in bank:
        raw,rows=c['triangulation'],c['coordinates'];ref=old[c['id']]
        a=normal_cut_handlebodies(raw,rows,record_certificate=True,lower_forest='source')
        b=normal_cut_handlebodies(raw,rows,record_certificate=True)
        assert a['status']==ref['weighted_status']
        record=dict(id=c['id'],source_status=a['status'],adaptive_status=b['status'],reason=b.get('reason'),
                    attempts=b['stats'].get('lower_forest_attempts'))
        if a['status']=='COMPLETE':
            assert digest(a['certificate'])==ref['certificate_sha256']
            assert verify_normal_cut_handlebodies(raw,rows,a['certificate'])
            assert b['status']=='COMPLETE' and a['census']==b['census'] and a['certificate']==b['certificate']
            counts['previous_certificates_unchanged']+=1
        counts[b['status']]+=1
        if b['status']=='COMPLETE':
            assert verify_normal_cut_handlebodies(raw,rows,b['certificate'])
            record.update(histogram=b['census']['histogram'],certificate_sha256=digest(b['certificate']))
            if a['status']!='COMPLETE':
                counts['new_complete']+=1
                record['new_certificate']=b['certificate']
                explicit=normal_cut_handlebodies(raw,rows,record_certificate=True,lower_forest='max_passages')
                assert explicit['certificate']==b['certificate']
        if a['status']!='COMPLETE' or 'source_three_handles' in ref:
            m=normal_cut_handlebodies(raw,rows,record_certificate=True,boundary_method='moments')
            assert m['status']==b['status']
            if m['status']=='COMPLETE':
                assert m['census']==b['census'] and verify_normal_cut_handlebodies(raw,rows,m['certificate'])
                counts['moment_replays']+=1
        try:
            proc=subprocess.run([sys.executable,'-m','marked_parallelity_research.audit_census','--oracle'],
                                input=json.dumps(c),text=True,capture_output=True,cwd=ROOT/'fast',timeout=30)
            assert proc.returncode==0,proc.stderr
            literal=json.loads(proc.stdout);record['regina']=literal
            if 'histogram' in literal:
                counts['literal_cuts']+=1
                if b['status']=='COMPLETE':
                    assert b['census']['histogram']==literal['histogram'];counts['literal_agreements']+=1
            else:counts['literal_expansion_cap']+=1
        except subprocess.TimeoutExpired:
            record['regina']=dict(status='TIMEOUT',seconds=30);counts['literal_timeouts']+=1
        records.append(record)
        if len(records)%10==0:print(len(records),dict(counts),flush=True)
    assert pins==sources()
    assert counts['previous_certificates_unchanged']==104 and counts['COMPLETE']==110 and counts['new_complete']==6
    report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                corpus_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                reference_sha256=hashlib.sha256(oldpath.read_bytes()).hexdigest(),counts=dict(counts),cases=records,
                oracle_scope='Fresh independent Regina source conversion, actual cutting and component recognition')
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(report),indent=2)+'\n')
    print(dict(counts),flush=True)


if __name__=='__main__':main()
