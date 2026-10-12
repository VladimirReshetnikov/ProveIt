"""Cross-check the source-pinned v5 publication artifacts, without rerunning timings."""
import hashlib
import json
from pathlib import Path
import statistics
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import encoded_integer
from normal_orbit_research.seeds import sources
DATA=Path(__file__).parent
read=lambda name:json.loads((DATA/(name+'.json')).read_text())
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
a=read('boundary-kernel-audit');b=read('boundary-kernel-benchmark')
d=read('boundary-kernel-direct-audit');p=read('core-three-handle-probe');old=read('core-annuli-audit')
pins=sources()
assert all(x['native_source_sha256']==pins for x in (a,b,d,p))
assert a['corpus_sha256']==b['corpus_sha256']==sha(ROOT/'fast/marked_parallelity_research/corpus.json')
assert b['driver_sha256']==sha(DATA/'boundary-kernel-benchmark.py')
assert d['source_audit_sha256']==sha(DATA/'boundary-kernel-audit.json')
before={c['id']:c for c in old['cases'] if c['native_status']=='COMPLETE'}
after={c['id']:c for c in a['cases'] if c['native_status']=='COMPLETE'}
assert len(before)==83 and len(after)==85
assert all(after[k]['certificate_sha256']==v['certificate_sha256'] for k,v in before.items())
assert set(after)-set(before)=={'fibonacci_lst_09/mixed','fibonacci_lst_10/mixed'}
assert len(b['cases'])==6 and b['rounds']==5 and len(b['capacity'])==2

def expected(source,n):
    genus,interior=(3,5) if source=='fibonacci_lst_09/mixed' else (2,3)
    return [dict(genus=0,multiplicity=n),dict(genus=genus,multiplicity=2)]+([] if n==1 else [dict(genus=interior,multiplicity=n-1)])

for c in b['cases']:
    assert c['schema']=='normal-cut-handlebodies-v5' and len(c['samples'])==5 and len(c['aa_ratios'])==3
    assert c['native_median']==statistics.median(s['native']['total'] for s in c['samples'])
    assert c['explicit_median']==statistics.median(s['explicit'] for s in c['samples'])
    assert c['median_paired_ratio']==statistics.median(s['explicit']/s['native']['total'] for s in c['samples'])
    assert c['aa_median']==statistics.median(c['aa_ratios'])
    assert c['histogram']==expected(c['source'],c['copies'])
for c in b['capacity']:
    assert c['schema']=='normal-cut-handlebodies-v5' and c['multiplicity_power']==16384
    decoded=[{k:encoded_integer(v) for k,v in row.items()} for row in c['census']]
    assert decoded==expected(c['source'],1<<16384)
assert len(d['cases'])==96 and d['certified']==sum(c['certified'] for c in d['cases'])
assert len(p['cases'])==10 and p['all_three_handles_removed']==10 and p['candidate_handlebody_censuses']==7
assert 'Ran 37 tests in 73.438s\n\nOK' in (DATA/'boundary-kernel-focused.txt').read_text()
log=(DATA/'boundary-kernel-tests.txt').read_text()
assert 'Ran 1678 tests in ' in log and '\n\nOK\n' in log and 'skipped=' not in log
names=['boundary-kernel-audit.json','boundary-kernel-audit.txt','boundary-kernel-focused.txt','boundary-kernel-tests.txt',
       'boundary-kernel-direct-audit.py','boundary-kernel-direct-audit.json','boundary-kernel-benchmark.py',
       'boundary-kernel-benchmark.json','boundary-kernel-benchmark.txt','core-three-handle-probe.py','core-three-handle-probe.json']
report=dict(scope='Publication consistency checks; no general complexity claim',runtime_source_pins_match=True,
            counts=a['counts'],previous_certificates_unchanged=83,focused_tests=37,full_tests=1678,
            direct_kernel_cases=len(d['cases']),direct_kernel_certificates=d['certified'],
            paired_benchmark_cases=6,capacity_cases=2,diagnostic_three_handle_cases=10,
            diagnostic_candidate_censuses=7,diagnostic_added_certificates=0,
            artifact_sha256={n:sha(DATA/n) for n in names},report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('Publication checks pass: 85 certified cuts, 83 unchanged earlier certificates.')
