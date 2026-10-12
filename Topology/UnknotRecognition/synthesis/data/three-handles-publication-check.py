"""Cross-check the source-pinned three-handle publication artifacts."""
import hashlib
import json
from pathlib import Path
import statistics
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from normal_orbit_research.seeds import sources
from fastunknot.integer_codec import encoded_integer
from fastunknot.column_cancellation_verify import verify_column_cancellations,verify_raw_cancellation_obstruction
read=lambda n:json.loads((DATA/(n+'.json')).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=read('three-handles-audit');c=read('three-handles-compatibility')
s=read('three-handles-source-audit');p=read('three-handles-choice-probe');b=read('three-handles-benchmark')
pins=sources()
assert all(x['native_source_sha256']==pins for x in (a,c,s,p,b))
assert a['corpus_sha256']==b['corpus_sha256']==sha(ROOT/'fast/marked_parallelity_research/corpus.json')
assert s['fixture_sha256']==p['fixture_sha256']==sha(ROOT/'fast/marked_parallelity_research/three_handle_corpus.json')
assert b['driver_sha256']==sha(DATA/'three-handles-benchmark.py')
assert a['counts']['COMPLETE']==a['counts']['independent_replays']==92
assert a['counts']['certified_regina_agreements']==85 and a['counts']['regina_expansion_cap']==7
assert len(c['cases'])==106 and c['unchanged_certificates']==85 and c['new_certificates']==7
old={r['id']:r for r in read('column-peeling-audit')['cases'] if r['native_status']=='COMPLETE'}
new={r['id']:r for r in a['cases'] if r['native_status']=='COMPLETE'}
assert all(new[k]['certificate_sha256']==v['certificate_sha256'] for k,v in old.items())
assert len(s['cases'])==14 and s['counts']=={'COMPLETE':10,'INCONCLUSIVE':4}
assert max(r['three_handles'] for r in s['cases'])==12
assert any(r['internal_chain_steps']>0 for r in s['cases']) and any(r['dual_loops']>0 for r in s['cases'])
assert len(p['cases'])==2 and all(len(r['trials'])==4 and sum(t['complete'] for t in r['trials'])==3 for r in p['cases'])
example=next(r for r in p['cases'] if r['id']=='interior_loop/empty')
assert example['source_columns']==[3,5,6,7,8]
counts={i:dict(zip(example['source_columns'],row)) for i,row in enumerate(example['source_matrix'])}
assert verify_raw_cancellation_obstruction(counts,[1,2,3,4])
assert verify_column_cancellations({i:r for i,r in counts.items() if i!=1},[[3,3],[2,8],[4,7],[0,6]])
assert b['finished'] and len(b['cases'])==9 and len(b['capacity'])==1
for r in b['cases']:
    assert len(r['samples'])==5 and len(r['aa_samples'])==3
    assert r['native_median']==statistics.median(x['native']['total'] for x in r['samples'])
    assert r['explicit_median']==statistics.median(x['explicit'] for x in r['samples'])
    assert r['paired_speedup']==statistics.median(x['explicit']/x['native']['total'] for x in r['samples'])
    assert r['aa_median']==statistics.median(x['ratio'] for x in r['aa_samples'])
assert [{k:encoded_integer(v) for k,v in row.items()} for row in b['capacity'][0]['histogram']]==[dict(genus=0,multiplicity=1<<16385)]
assert b['capacity'][0]['multiplicity_power']==16384 and b['capacity'][0]['hex_replay_seconds']>0
assert 'Ran 33 tests in 73.185s\n\nOK' in (DATA/'three-handles-focused.txt').read_text()
log=(DATA/'three-handles-tests.txt').read_text()
assert 'Ran 1696 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
names=['three-handles-audit.json','three-handles-audit.txt','three-handles-source-audit.py',
       'three-handles-source-audit.json','three-handles-source-audit.txt','three-handles-choice-probe.py',
       'three-handles-choice-probe.json','three-handles-compatibility.py','three-handles-compatibility.json',
       'three-handles-compatibility.txt','three-handles-focused.txt','three-handles-tests.txt',
       'three-handles-benchmark.py','three-handles-benchmark.json','three-handles-benchmark.txt']
report=dict(scope='Source two/three elimination and supplied-cut certificates; not general recognition',
            runtime_source_pins_match=True,focused_tests=33,full_tests=1696,source_cases=106,
            complete_cuts=92,previous_certificates_unchanged=85,literal_agreements=85,
            added_source_cases=14,added_source_complete_cuts=10,alternative_loop_certificates=6,
            paired_benchmark_cases=9,capacity_cases=1,
            artifact_sha256={n:sha(DATA/n) for n in names},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 92 certified cuts, 85 unchanged proofs, 14 additional source fixtures.')
