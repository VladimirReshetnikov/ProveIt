"""Check native deferred discovery, source certificates and retained evidence."""
from collections import Counter
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
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare,_coordinates
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((DATA/(n+'.json')).read_text())
a=read('deferred-forest-audit');b=read('deferred-forest-benchmark');c=read('deferred-forest-coupled-probe')
f=read('deferred-forest-benchmark-followup')
assert a['native_source_sha256']==b['native_source_sha256']==c['native_source_sha256']==f['native_source_sha256']==sources()
paths=[ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
assert a['corpus_sha256']==b['corpus_sha256']==f['corpus_sha256']=={p.name:sha(p) for p in paths}
assert a['reference_sha256']==sha(DATA/'lower-forest-audit.json')
for name in ('deferred-forest-audit','deferred-forest-benchmark','deferred-forest-coupled-probe','deferred-forest-benchmark-followup'):
    assert read(name)['driver_sha256']==sha(DATA/(name+'.py'))
expected={p.name:sha(p) for p in (DATA/'deferred-forest-baseline').glob('*.py')}
assert b['baseline_sha256']==f['baseline_sha256']==expected
for p in (DATA/'deferred-forest-baseline').glob('*.py'):
    assert p.read_bytes()==subprocess.check_output(['git','show','0feb251bd5601ae0f325900d35e8c98e16e21413:Topology/UnknotRecognition/fast/fastunknot/'+p.name])
changed=subprocess.check_output(['git','diff','--name-only','0feb251bd5601ae0f325900d35e8c98e16e21413','--','Topology/UnknotRecognition/fast/fastunknot'],cwd=ROOT.parents[1],text=True).splitlines()
assert {Path(p).name for p in changed}=={'core_handlebody.py','bundle_boundary_kernel.py','normal_cut_handlebodies.py'}
assert a['counts']==dict(previous_certificates_unchanged=110,COMPLETE=111,explicit_deferred_COMPLETE=111,
    literal_cuts=113,literal_agreements=104,moment_replays=20,INCONCLUSIVE=9,explicit_deferred_INCONCLUSIVE=9,
    new_complete=1,literal_expansion_cap=7)
new=[r for r in a['cases'] if 'new_certificate' in r]
assert len(new)==1 and new[0]['id']=='pachner23_5_8_2/mixed'
p=new[0]['new_certificate'];g=p['parallelity']['geometry']
assert verify_normal_cut_handlebodies(g['source'],g['coordinates'],p)
assert p['schema']=='normal-cut-handlebodies-v2'
for report,size in ((b,8),(f,1)):
    assert report['finished'] and len(report['cases'])==size
    for r in report['cases']:
        assert len(r['samples'])==5 and len(r['aa_samples'])==3
        for mode in ('before','after'):
            assert r[mode+'_median']==statistics.median(s[mode]['total'] for s in r['samples'])
        expected=statistics.median(s['before']['total']/s['after']['total'] for s in r['samples']) if r['comparable_successes'] else None
        assert r['paired_speedup']==expected
        assert r['aa_median']==statistics.median(s['ratio'] for s in r['aa_samples'])
assert sum(r['comparable_successes'] for r in b['cases'])==4
assert f['cases'][0]['id']=='fibonacci_lst_09/mixed'
assert c['counts']==dict(SUCCESS=114,source_positive_replays=114,INCONCLUSIVE=4,NO_FOREST=2,independent_packing_obstructions=2)
assert c['budgets']==dict(max_work=100000,max_partitions=500)
assert c['delivered_source_sha256']=={p.name:sha(p) for p in (ROOT/'reports/105/finite_selector').glob('*.py')}
bank={r['id']:r for p in paths for r in json.loads(p.read_text())['cases']}
for row in c['cases']:
    source=bank[row['id']];p=_prepare(source['triangulation'],lambda:None)
    g=_reference_parallelity(p,_coordinates(p,source['coordinates'],lambda:None),lambda:None)
    raw=[dict(Counter(x['handle'] for x in h['cycle'] if x['dimension']==1)) for h in g['core']['handles2']]
    assert row['problem']['rows']==[[list(pair) for pair in sorted(r.items())] for r in raw]
    if row['result']['status']=='SUCCESS':
        reduced=replay_core_three_handles(g,row['top_certificate']);assert reduced is not None
        assert verify_core_handlebody_certificate(reduced['core'],row['core_certificate'])
    if row['result']['status']=='NO_FOREST':
        proof=row['independent_stopping_packing'];groups=proof['row_sets'];used=set()
        assert proof['maximum_top_deletions']==len(g['core']['handles3'])<len(groups)
        for group in groups:
            assert group and len(group)==len(set(group)) and not used.intersection(group);used.update(group)
            sums=Counter()
            for r in group:assert 0<=r<len(raw);sums.update(raw[r])
            assert all(v!=1 for v in sums.values())
gap=read('deferred-forest-report106-gap-review')
assert gap['tests']==6 and gap['seconds']==0.106
assert gap['patch_sha256']==sha(ROOT/'reports/106/integration/orbit-contraction.patch')
assert all(r['unchanged'] and r['current_sha256']==r['baseline_sha256']==sha(ROOT/'fast/fastunknot'/name) for name,r in gap['targets'].items())
assert 'Ran 6 tests in 0.106s\n\nOK' in (DATA/'deferred-forest-report106-gap-tests.txt').read_text()
assert 'Ran 46 tests in 85.016s\n\nOK' in (DATA/'deferred-forest-focused.txt').read_text()
log=(DATA/'deferred-forest-tests.txt').read_text()
assert 'Ran 1729 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
artifacts=sorted(p for p in DATA.glob('deferred-forest-*') if p.is_file() and p!=Path(__file__).with_suffix('.json'))
report=dict(scope='Complete lower-forest discovery for fixed admitted raw matrices; global quasi-polynomial recognition unproved',
    sources_match=True,all_native_checkers_unchanged=True,full_tests=1729,focused_tests=46,
    source_cases=120,complete_cuts=111,previous_certificates_unchanged=110,fresh_literal_agreements=104,
    closed_walk_exhaustive_forest_cases=160,coupled_source_positive_replays=114,
    independent_all_forest_packing_obstructions=2,
    artifact_sha256={p.name:sha(p) for p in artifacts},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 111 cuts, 104 fresh literal agreements, 1729 tests, unchanged verifiers.')
