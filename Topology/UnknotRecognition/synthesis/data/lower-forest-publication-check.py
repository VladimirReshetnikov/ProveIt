"""Bind the lower-forest claims to retained baselines, sources and fresh evidence."""
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
a=read('lower-forest-audit');b=read('lower-forest-benchmark')
assert a['native_source_sha256']==b['native_source_sha256']
revision=read('lower-forest-test-revisions');updated=dict(a['native_source_sha256'])
assert set(revision['files'])=={'fast/tests/test_core_primitive_annuli.py','fast/tests/test_disk_bundle_absorption.py'}
for name,r in revision['files'].items():
    assert updated[name]==r['before_sha256']
    assert sha(ROOT/name)==r['after_sha256']
    updated[name]=r['after_sha256']
assert updated==sources()
assert a['corpus_sha256']==b['corpus_sha256']=={n:sha(ROOT/'fast/marked_parallelity_research'/n)
    for n in ('corpus.json','three_handle_corpus.json')}
assert a['reference_sha256']==sha(DATA/'weighted-forest-audit.json')
for name in ('lower-forest-audit','lower-forest-benchmark'):
    assert read(name)['driver_sha256']==sha(DATA/(name+'.py'))
assert b['baseline_sha256']=={f.name:sha(f) for f in (DATA/'lower-forest-baseline').glob('*.py')}
for f in (DATA/'lower-forest-baseline').glob('*.py'):
    original=subprocess.check_output(['git','show','ac9c845a5c507c5d7a17d45b2d8de84fc046d455:Topology/UnknotRecognition/fast/fastunknot/'+f.name])
    assert f.read_bytes()==original
for name in ('core_three_handle_reduction_verify.py','normal_cut_handlebodies_verify.py','core_handlebody_verify.py'):
    original=subprocess.check_output(['git','show','ac9c845a5c507c5d7a17d45b2d8de84fc046d455:Topology/UnknotRecognition/fast/fastunknot/'+name])
    assert (ROOT/'fast/fastunknot'/name).read_bytes()==original
counts=a['counts']
for key,n in dict(previous_certificates_unchanged=104,COMPLETE=110,new_complete=6,
                  INCONCLUSIVE=10,literal_cuts=113,literal_agreements=103,literal_expansion_cap=7).items():
    assert counts[key]==n
assert not counts.get('literal_timeouts',0)
new=[r for r in a['cases'] if r['source_status']!='COMPLETE' and r['adaptive_status']=='COMPLETE']
assert {r['id'] for r in new}=={'pilot/fibonacci_lst_04/0','pilot/fibonacci_lst_06/0',
    'pilot/fibonacci_lst_08/0','pilot/fibonacci_lst_10/0','pilot/lst_4_9/0','pilot/finite_trefoil/0'}
for r in new:
    p=r['new_certificate'];g=p['parallelity']['geometry']
    assert verify_normal_cut_handlebodies(g['source'],g['coordinates'],p)
    assert hashlib.sha256(json.dumps(p,sort_keys=True).encode()).hexdigest()==r['certificate_sha256']
    if r['id'] in ('pilot/fibonacci_lst_08/0','pilot/fibonacci_lst_10/0'):
        assert p['kernel']['schema']=='bundle-boundary-kernel-v3'
assert b['finished'] and len(b['cases'])==8
for r in b['cases']:
    assert len(r['samples'])==5 and len(r['aa_samples'])==3
    for mode in ('source','adaptive'):
        assert r[mode+'_median']==statistics.median(s[mode]['total'] for s in r['samples'])
    expected=statistics.median(s['source']['total']/s['adaptive']['total'] for s in r['samples']) if r['comparable_successes'] else None
    assert r['paired_speedup']==expected
    assert r['aa_median']==statistics.median(s['ratio'] for s in r['aa_samples'])
assert sum(r['comparable_successes'] for r in b['cases'])==4
assert 'Ran 36 tests in 73.850s\n\nOK' in (DATA/'lower-forest-focused.txt').read_text()
log=(DATA/'lower-forest-tests.txt').read_text()
assert 'Ran 1723 tests in ' in log and 'FAILED (failures=2)' in log and 'skipped=' not in log
assert log.count('FAIL: ')==2 and 'ERROR: ' not in log
assert 'FAIL: test_binary_multiplicity_and_remaining_failures' in log
assert 'FAIL: test_nondisk_annuli_and_stalled_augmented_cores_remain_unresolved' in log
fixed=(DATA/'lower-forest-corrected-fixtures.txt').read_text()
assert 'Ran 2 tests in ' in fixed and '\n\nOK\n' in fixed
probe=read('lower-forest-deferred-probe')
assert probe['native_source_sha256']==sources()
assert probe['driver_sha256']==sha(DATA/'lower-forest-deferred-probe.py')
assert probe['counts']==dict(COMPLETE=118,new_vs_canonical_reduced_core=6,INCONCLUSIVE=2)
assert probe['delivered_whole_gains_over_current']==['pachner23_5_8_2/mixed']
packets=read('lower-forest-report105-packets')
assert packets['status']=='VERIFIED' and len(packets['whole_cut_packets'])==9 and len(packets['core_packets'])==8
selector=read('lower-forest-report105-selector')
assert selector['counts']==dict(exhaustive_3x2=46656,no_forest=45475,success=5183,random_general=2000,random_cycle_compatible=2000,edge_cases=2)
assert selector['mismatches']==0
assert 'Ran 11 tests in 8.864s\n\nOK' in (DATA/'lower-forest-report105-tests.txt').read_text()
artifacts=sorted(f for f in DATA.glob('lower-forest-*') if f.is_file() and f!=Path(__file__).with_suffix('.json'))
report=dict(scope='Frozen lower-forest optimization and two finite attempts; no general recognition completeness',
    source_pins_match=True,unchanged_checkers=['core_three_handle_reduction','core_handlebody','normal_cut_handlebodies'],
    changed_checker='bundle_boundary_kernel: independently authenticate supplied v3 forest; preserve v1/v2 semantics',
    full_test_inventory=1723,initial_historical_fixture_failures=2,corrected_fixture_tests=2,focused_tests=36,graph_optimality_cases=200,source_cases=120,complete_cuts=110,
    new_complete_cuts=6,previous_certificates_unchanged=104,fresh_literal_agreements=103,benchmark_cases=8,
    artifact_sha256={f.name:sha(f) for f in artifacts},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 110 complete cuts, 103 fresh literal agreements, 1723 tests validated across the full run and two corrected fixture reruns.')
