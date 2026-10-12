"""Check the source-pinned weighted-forest publication and compatibility claims."""
import hashlib
import json
from pathlib import Path
import statistics
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from normal_orbit_research.seeds import sources
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((DATA/(n+'.json')).read_text())
a=read('weighted-forest-audit');b=read('weighted-forest-benchmark');p=read('weighted-forest-degree-two-probe')
primal=read('weighted-forest-primal-probe')
assert a['native_source_sha256']==b['native_source_sha256']==p['native_source_sha256']==sources()
assert primal['native_source_sha256']==sources()
assert primal['reference_sha256']==sha(DATA/'weighted-forest-audit.json')
assert len(primal['new_bare_core_completions'])==6 and len(primal['new_experimental_whole_cuts'])==4
experimental=0
for row in primal['cases']:
    for trial in row['trials']:
        if trial.get('whole_replay'):
            proof=trial['whole_certificate'];g=proof['parallelity']['geometry']
            assert verify_normal_cut_handlebodies(g['source'],g['coordinates'],proof)
            experimental+=1
assert experimental==8
assert a['corpus_sha256']==b['corpus_sha256']=={n:sha(ROOT/'fast/marked_parallelity_research'/n)
    for n in ('corpus.json','three_handle_corpus.json')}
assert a['reference_sha256']==sha(DATA/'moment-boundary-audit.json')
assert b['driver_sha256']==sha(DATA/'weighted-forest-benchmark.py')
assert b['baseline_sha256']=={f.name:sha(f) for f in (DATA/'weighted-forest-baseline').glob('*.py')}
assert a['counts']==dict(queue_certificates_unchanged=102,COMPLETE=104,weighted_certificates_unchanged=85,
    literal_cuts=113,literal_agreements=97,INCONCLUSIVE=16,lower_retained_cost=23,
    moment_replays=19,literal_expansion_cap=7,new_complete=2)
assert len(a['cases'])==120
assert [r['id'] for r in a['cases'] if r['queue_status']!='COMPLETE' and r['weighted_status']=='COMPLETE']==[
    'interior_loop/empty','interior_loop/boundary_link']
assert all(r['weighted_status']=='COMPLETE' for r in a['cases'] if r['queue_status']=='COMPLETE')
assert sum(r['source_three_handles']>0 for r in a['cases'] if 'source_three_handles' in r)==24
assert p['counts']==dict(SUCCESS=83,INCONCLUSIVE=35,NO_FOREST=2)
assert not any(r['result']['status']=='SUCCESS' and not r['weighted_core_complete'] for r in p['cases'])
assert p['delivered_source_sha256']=={f.name:sha(f) for f in sorted((ROOT/'reports/99/code/forest_search').glob('*.py'))}
for name in ('core_three_handle_reduction_verify.py','normal_cut_handlebodies_verify.py','bundle_boundary_kernel_verify.py'):
    path=ROOT/'fast/fastunknot'/name
    original=subprocess.check_output(['git','show','97e16378b:Topology/UnknotRecognition/fast/fastunknot/'+name])
    assert path.read_bytes()==original
assert b['finished'] and len(b['cases'])==8
for r in b['cases']:
    assert len(r['samples'])==5 and len(r['aa_samples'])==3
    for mode in ('queue','weighted'):
        assert r[mode+'_median']==statistics.median(s[mode]['total'] for s in r['samples'])
    expected=statistics.median(s['queue']['total']/s['weighted']['total'] for s in r['samples']) if r['comparable_successes'] else None
    assert r['paired_speedup']==expected
    assert r['aa_median']==statistics.median(s['ratio'] for s in r['aa_samples'])
assert sum(r['comparable_successes'] for r in b['cases'])==6
assert 'Ran 19 tests in 20.486s\n\nOK' in (DATA/'weighted-forest-focused.txt').read_text()
assert 'Ran 18 tests in 0.004s\n\nOK' in (DATA/'weighted-forest-delivered99-tests.txt').read_text()
log=(DATA/'weighted-forest-tests.txt').read_text()
assert 'Ran 1716 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
artifacts=sorted(f for f in DATA.glob('weighted-forest-*') if f.is_file() and f!=Path(__file__).with_suffix('.json'))
report=dict(scope='Exact fixed additive dual-tree objective; no general cancellation or recognition completeness',
    source_pins_match=True,independent_checkers_unchanged=True,full_tests=1716,focused_tests=19,
    graph_optimality_cases=400,source_cases=120,complete_cuts=104,new_complete_cuts=2,
    queue_certificates_unchanged=102,weighted_certificates_unchanged=85,fresh_literal_agreements=97,
    restricted_solver_bare_core_gain=0,benchmark_cases=8,experimental_lower_forest_cuts=4,
    independently_replayed_experimental_certificates=8,
    artifact_sha256={f.name:sha(f) for f in artifacts},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 104 complete cuts, 97 fresh literal agreements, 1716 tests.')
