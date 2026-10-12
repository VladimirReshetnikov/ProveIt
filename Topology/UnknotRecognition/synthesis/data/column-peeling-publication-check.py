"""Check publication consistency and source pins without rerunning benchmarks."""
import hashlib
import json
from pathlib import Path
import statistics
import sys
ROOT=Path(__file__).resolve().parents[2]
DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from normal_orbit_research.seeds import sources
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((DATA/(n+'.json')).read_text())
a=read('column-peeling-audit');c=read('column-peeling-compatibility');b=read('column-peeling-benchmark')
pins=sources()
assert all(x['native_source_sha256']==pins for x in (a,c,b))
assert a['corpus_sha256']==b['corpus_sha256']==sha(ROOT/'fast/marked_parallelity_research/corpus.json')
assert b['driver_sha256']==sha(DATA/'column-peeling-benchmark.py')
assert b['baseline_sha256']=={p.name:sha(p) for p in sorted((DATA/'column-baseline').glob('*.py'))}
assert b['finished'] and b['rounds']==5 and len(b['cases'])==14
assert a['counts']['COMPLETE']==85 and a['counts']['independent_replays']==85
assert a['counts']['certified_regina_agreements']==78 and a['counts']['regina_expansion_cap']==7
assert c['complete']==85 and c['skipped_boundaries']==6 and c['unchanged_certificates']==44
assert len(a['cases'])==len(c['cases'])==106
byid={r['id']:r for r in a['cases']}
assert all(byid[r['id']]['native_status']==r['status'] for r in c['cases'])
for r in b['cases']:
    assert len(r['samples'])==5 and len(r['aa_samples'])==3
    assert r['old_median']==statistics.median(s['old'] for s in r['samples'])
    assert r['new_median']==statistics.median(s['new'] for s in r['samples'])
    assert r['paired_speedup']==statistics.median(s['old']/s['new'] for s in r['samples'])
    assert r['aa_median']==statistics.median(s['ratio'] for s in r['aa_samples'])
    if r['label'].startswith('matrix-chain-'):
        assert r['new_work']['entry_updates']==0
        assert r['new_work']['incidence_visits']==r['incidences']==2*r['rows']
assert 'Ran 54 tests in 80.515s\n\nOK' in (DATA/'column-peeling-focused.txt').read_text()
log=(DATA/'column-peeling-tests.txt').read_text()
assert 'Ran 1688 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
names=['column-peeling-audit.json','column-peeling-audit.txt','column-peeling-compatibility.py',
       'column-peeling-compatibility.json','column-peeling-compatibility.txt','column-peeling-focused.txt',
       'column-peeling-tests.txt','column-peeling-benchmark.py','column-peeling-benchmark.json',
       'column-peeling-benchmark.txt']
report=dict(scope='Local cancellation and complete supplied-cut evidence; no general recognition bound',
            runtime_source_pins_match=True,focused_tests=54,full_tests=1688,
            source_cases=106,complete_cuts=85,literal_agreements=78,legacy_replays=85,
            unchanged_certificates=44,boundary_queries_skipped=6,paired_benchmark_cases=14,
            artifact_sha256={n:sha(DATA/n) for n in names},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 85 preserved cut censuses; 85 old proofs replay; six early refusals.')
