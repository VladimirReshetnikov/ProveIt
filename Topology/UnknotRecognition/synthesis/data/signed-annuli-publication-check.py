"""Bind signed-annulus publication claims to source, fixtures and raw evidence."""
import hashlib,json,re,statistics
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((DATA/(n+'.json')).read_text())
current={p.name:sha(p) for p in (ROOT/'fast/fastunknot').glob('*.py')}
audit=read('signed-annuli-audit');replay=read('signed-annuli-replay')
assert audit['passed'] and replay['passed']
assert audit['source_sha256']==replay['source_sha256']==current
assert (audit['cases'],audit['before'],audit['after'])==(126,112,117)
assert len(audit['records'])==126 and len({r['id'] for r in audit['records']})==126
for row in audit['records']:
    if row['before']['status']=='COMPLETE':
        assert row['before']['certificate_sha256']==row['after']['certificate_sha256']
    if row['after']['status']=='COMPLETE':assert row['after']['replayed']
assert len(audit['added'])==len(audit['literal_oracles'])==5
assert all(o['histogram']==[dict(genus=2,multiplicity=2)] for o in audit['literal_oracles'])
for name,digest in audit['corpus_sha256'].items():assert sha(ROOT/'fast'/name)==digest
assert replay['packets']==5
for r in replay['records']:
    assert r['verified']
    assert r['packet_sha256']==sha(ROOT/'reports/114/results/certificates'/(r['id'].replace('/','__')+'.json'))
base=read('signed-annuli-baseline')
assert base['verified_against_git_archive'] and base['pin'].startswith(audit['baseline_pin'])
assert base['additional_fixture_sha256']==sha(ROOT/'fast/signed_annulus_research/corpus.json')
algebra=read('signed-annuli-algebra');assert algebra['passed']
assert algebra['audit_script_sha256']==sha(DATA/'signed-annuli-algebra-audit.py')
assert not algebra['production_files_changed_during_run']
for name,digest in algebra['production_sha256'].items():assert current[name]==digest
assert (algebra['counts']['exhaustive_single'],algebra['counts']['exhaustive_pair'],
        algebra['counts']['positive_certificates_checked'],algebra['counts']['compiler_sequences'])==(1104,6576,1284,396)
assert algebra['corruption_counts']['accepted']==4 and algebra['corruption_counts']['rejected']==91
log=(DATA/'signed-annuli-tests.txt').read_text()
assert re.search(r'Ran 1798 tests in [0-9.]+s\n\nOK',log),log[-400:]
assert not re.search(r'\.\.\. (FAIL|ERROR|skipped)',log)
focused=(DATA/'signed-annuli-focused.txt').read_text()
assert re.search(r'Ran 25 tests in [0-9.]+s\n\nOK',focused)
assert 'test_exact_integer_transport_and_malformed_exponents' in focused
bench=read('signed-annuli-benchmark');assert bench['passed'] and bench['source_sha256']==current
assert len(bench['records'])==8 and sum(r['comparable'] for r in bench['records'])==3
for r in bench['records']:
    assert len(r['samples'])==7 and len(r['aa'])==3
    assert r['before_median']==statistics.median(s['before']['total'] for s in r['samples'])
    assert r['after_median']==statistics.median(s['after']['total'] for s in r['samples'])
    assert r['paired_latency_ratio']==statistics.median(s['before']['total']/s['after']['total'] for s in r['samples'])
    if r['comparable']:
        assert all(s['before']['certificate_sha256']==s['after']['certificate_sha256'] for s in r['samples'])
repeat=read('signed-annuli-benchmark-repeat')
assert repeat['passed'] and repeat['source_sha256']==current and len(repeat['records'])==1
r=repeat['records'][0]
assert r['id']=='pilot/fibonacci_lst_08/0' and len(r['samples'])==21 and len(r['aa'])==7
assert r['paired_latency_ratio']==statistics.median(s['before']['total']/s['after']['total'] for s in r['samples'])
table=(DATA/'signed-annuli-native-table.tex').read_text()
for row in bench['records']:
    ratio=f"{row['paired_latency_ratio']:.3f}" if row['comparable'] else '--'
    numbers=f"& {1000*row['before_median']:.2f} & {1000*row['after_median']:.2f} & {ratio} & {row['aa_ratio']:.3f}"
    assert numbers in table
compression=read('signed-annuli-compression')
for name,digest in compression['production_sha256'].items():assert current[name]==digest
assert len(compression['results'])==22 and all(r['status']=='COMPLETE' for r in compression['results'])
for r in compression['results']:
    if r['status']=='COMPLETE':
        assert r['verified'] and len(r['complete_query_seconds_samples'])==r['repetitions']
        assert r['complete_query_seconds_median']==statistics.median(r['complete_query_seconds_samples'])
    else:assert r['status']=='BUDGET'
table=(DATA/'signed-annuli-compression-table.tex').read_text()
for r in compression['results']:
    if r['parameter']==2048 or (r['family']=='independent_blocks' and r['parameter']==64):
        numbers=f"& {r['expanded_length_bits']} & {r['source_nodes']} & {r['producer_nodes']} & {1000*r['complete_query_seconds_median']:.2f}"
        assert numbers in table
latex=(DATA/'signed-annuli-latex-final.txt').read_text()
assert 'Output written on report.pdf' in latex
assert 'undefined references' not in latex and 'undefined on input line' not in latex
article=(ROOT/'synthesis/signed_primitive_annuli.tex').read_text()
assert '1798' in article and '117' in article and '112' in article
result=dict(passed=True,cases=126,old_positive_certificates_unchanged=112,current_positives=117,
            saved_packets=5,broad_tests_before_codec_fix=1798,focused_tests_after_codec_fix=25,
            current_distinct_tests=1799,source_sha256=current,
            report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='source_sha256'}))
