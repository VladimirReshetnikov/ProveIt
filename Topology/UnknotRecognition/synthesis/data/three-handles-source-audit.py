"""Independent expanded cuts for the additional nested and loop fixtures."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from marked_parallelity_research.audit_census import oracle
from normal_orbit_research.seeds import sources
pins=sources();path=ROOT/'fast/marked_parallelity_research/three_handle_corpus.json'
bank=json.loads(path.read_text())['cases'];records=[]
for c in bank:
    raw,rows=c['triangulation'],c['coordinates']
    p=normal_cut_parallelity(raw,rows);g=p['geometry'];reduced,proof=reduce_core_three_handles(g)
    assert replay_core_three_handles(g,proof)==reduced
    ends={r['two_handle']:r['ends'] for r in proof['dual_endpoints']}
    result=normal_cut_handlebodies(raw,rows,record_certificate=True);reference=oracle(c)
    if result['status']=='COMPLETE':
        assert verify_normal_cut_handlebodies(raw,rows,result['certificate'])
        assert result['census']['histogram']==reference['histogram']
    record=dict(id=c['id'],tetrahedra=len(raw['tetrahedra']),three_handles=len(g['core']['handles3']),
                moves=proof['cancellations'],dual_loops=sum(a is not None and a==b for a,b in ends.values()),
                internal_chain_steps=sum(all(v is not None for v in ends[m['two_handle']]) for m in proof['cancellations']),
                status=result['status'],native_histogram=result.get('census',{}).get('histogram'),regina=reference)
    records.append(record);print(c['id'],record['status'],reference['histogram'],flush=True)
assert pins==sources()
report=dict(native_source_sha256=pins,fixture_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            cases=records,counts=dict(Counter(r['status'] for r in records)))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
