"""Research-only deferred primal discovery on current weighted top reductions.

Report 105 supplies the bridge argument. No producer or checker is patched;
this probe supplies its discovered forest to the ordinary native core API.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_handlebody import _occurrences, column_cancellation_plan, core_handlebody_certificate
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.seeds import sources


def main():
    pins=sources();counts=Counter();records=[]
    paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
    bank=[c for p in paths for c in json.loads(p.read_text())['cases']]
    for case in bank:
        p=_prepare(case['triangulation'],lambda:None)
        g=_parallelity_geometry(p,_coordinates(p,case['coordinates'],lambda:None),lambda:None)
        reduced,top=reduce_core_three_handles(g,strategy='max_weight')
        core=reduced['core'];n=len(core['handles0'])
        for h in core['handles2']:
            parity=[0]*n
            for flag in h['cycle']:
                if flag['dimension']==1:
                    for v in core['handles1'][flag['handle']]['ends']:parity[v]^=1
            assert not any(parity)
        rows=_occurrences(core,(),lambda:None);planned=column_cancellation_plan(rows)
        forbidden={e for _,e in planned['cancellations']};labels=list(range(n));tree=[]
        for h in core['handles1']:
            if h['id'] in forbidden:continue
            a,b=(labels[v] for v in h['ends'])
            if a!=b:
                tree.append(h['id']);labels=[min(a,b) if x in (a,b) else x for x in labels]
        assert all(labels[h['ends'][0]]==labels[h['ends'][1]] for h in core['handles1'])
        # Independent direct column-total replay of the partial discovery trace.
        live=set(rows)
        for r,e in planned['cancellations']:
            assert r in live and rows[r].get(e)==1 and sum(rows[k].get(e,0) for k in live)==1
            live.remove(r)
        assert live==set(planned['remaining_rows'])
        assert all(sum(rows[r].get(e,0) for r in live)!=1 for e in range(len(core['handles1'])))
        result=core_handlebody_certificate(core,forest=tree)
        assert (result['status']=='COMPLETE')==(not bool(live))
        if result['status']=='COMPLETE':assert verify_core_handlebody_certificate(core,result['certificate'])
        canonical=core_handlebody_certificate(core)
        counts[result['status']]+=1
        if canonical['status']!='COMPLETE' and result['status']=='COMPLETE':counts['new_vs_canonical_reduced_core']+=1
        records.append(dict(id=case['id'],source_three_handles=len(g['core']['handles3']),
            canonical_core_status=canonical['status'],deferred_core_status=result['status'],
            forest=tree,pivots=planned['cancellations'],remaining_rows=sorted(live)))
    assert sources()==pins
    audit=json.loads((DATA/'lower-forest-audit.json').read_text());old={r['id']:r for r in audit['cases']}
    extra=[]
    for p in (ROOT/'reports/105/certificates/whole_cut').glob('*.json'):
        packet=json.loads(p.read_text());key=packet['source']['id']
        assert packet['certificate']['census']['histogram']==old[key]['regina']['histogram']
        if old[key]['adaptive_status']!='COMPLETE':extra.append(key)
    report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        counts=dict(counts),cases=records,delivered_whole_gains_over_current=sorted(extra),
        scope='Research only: current weighted top reduction, deferred source lower forest, no annular consumer integration')
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(dict(counts));print('Delivered additional whole cuts:',extra)


if __name__=='__main__':main()
