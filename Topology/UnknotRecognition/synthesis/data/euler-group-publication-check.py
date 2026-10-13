"""Check current source, all coverage records and the published timing table."""
import ast
import hashlib
import json
from pathlib import Path
import re
import statistics
ROOT=Path(__file__).resolve().parents[2]
DATA=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda name:json.loads((DATA/(name+'.json')).read_text())
current={p.name:sha(p) for p in (ROOT/'fast/fastunknot').glob('*.py')}


class WithoutDocstrings(ast.NodeTransformer):
    def visit_Module(self,node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):
            node.body=node.body[1:]
        return node
    visit_FunctionDef=visit_Module
    visit_AsyncFunctionDef=visit_Module
    visit_ClassDef=visit_Module


def executable(path):return ast.dump(WithoutDocstrings().visit(ast.parse(path.read_text())),include_attributes=False)


old=DATA/'euler-group-tested-wrapper.py'
assert executable(old)==executable(ROOT/'fast/fastunknot/normal_cut_handlebodies.py')
for name in ('euler-group-audit','euler-group-replay'):
    report=read(name)
    assert report['passed']
    for file,digest in report['source_sha256'].items():
        assert digest==current[file] or (file=='normal_cut_handlebodies.py' and digest==sha(old))
    assert set(report['source_sha256'])==set(current)
audit=read('euler-group-audit'); replay=read('euler-group-replay')
assert (audit['cases'],audit['before'],audit['after'])==(120,111,112)
assert len(audit['records'])==120 and len({r['id'] for r in audit['records']})==120
assert audit['added']==['pilot/finite_figureEight/0']
for r in audit['records']:
    if r['before']['status']=='COMPLETE':
        assert r['before']['certificate_sha256']==r['after']['certificate_sha256']
    if r['after']['status']=='COMPLETE':assert r['after']['replayed']
assert replay['packets']==76 and all(r['verified'] for r in replay['records'])
for r in replay['records']:assert r['sha256']==sha(ROOT/'reports/111/certificates/group'/r['file'])
baseline=read('euler-group-baseline')
assert baseline['verified_against_git_archive'] and baseline['pin'].startswith(audit['baseline_pin'])
for name,digest in baseline['corpus_sha256'].items():
    assert sha(ROOT/'fast/marked_parallelity_research'/name)==digest
packet=read('euler-group-figure-eight')
encoded=json.dumps(packet['certificate'],sort_keys=True,separators=(',',':')).encode()
new=next(r for r in audit['records'] if r['id']==packet['source']['id'])
assert hashlib.sha256(encoded).hexdigest()==new['after']['certificate_sha256']
bench=read('euler-group-benchmark');assert bench['passed'] and bench['source_sha256']==current
assert len(bench['records'])==5
for r in bench['records']:
    assert len(r['samples'])==7 and len(r['aa'])==3
    assert r['before_median']==statistics.median(s['before']['total'] for s in r['samples'])
    assert r['after_median']==statistics.median(s['after']['total'] for s in r['samples'])
    assert r['paired_latency_ratio']==statistics.median(s['before']['total']/s['after']['total'] for s in r['samples'])
    if r['comparable']:
        for s in r['samples']:assert s['before']['certificate_sha256']==s['after']['certificate_sha256']
log=(DATA/'euler-group-tests.txt').read_text()
assert re.search(r'Ran 1774 tests in [0-9.]+s\n\nFAILED \(failures=2\)',log),log[-300:]
assert log.count(' ... FAIL')==2 and not re.search(r'\.\.\. (ERROR|skipped)',log)
assert 'FAIL: test_six_new_sources_both_boundary_methods (test_lower_forests.LowerForestTests.test_six_new_sources_both_boundary_methods)' in log
assert 'FAIL: test_two_new_loop_cuts_both_boundary_backends (test_weighted_top_forest.WeightedTopForestTests.test_two_new_loop_cuts_both_boundary_backends)' in log
rerun=(DATA/'euler-group-policy-rerun.txt').read_text()
assert re.search(r'Ran 2 tests in [0-9.]+s\n\nOK\s*$',rerun)
assert 'test_six_new_sources_both_boundary_methods' in rerun
table=(DATA/'euler-group-table.tex').read_text()
for row in bench['records']:
    ratio=f"{row['paired_latency_ratio']:.3f}" if row['comparable'] else '--'
    numbers=f"& {1000*row['before_median']:.2f} & {1000*row['after_median']:.2f} & {ratio} & {row['aa_ratio']:.3f}"
    assert numbers in table
latex=(DATA/'euler-group-latex-final.txt').read_text()
assert 'Output written on report.pdf' in latex
assert 'undefined references' not in latex and 'undefined on input line' not in latex
article=(ROOT/'synthesis/euler_group_terminal.tex').read_text()
assert '1774' in article and '112' in article and '111' in article
result=dict(passed=True,cases=120,old_positive_certificates_unchanged=111,current_positives=112,
            saved_packets=76,tests=1774,broad_passed=1772,corrected_policy_rerun_passed=2,source_sha256=current,
            docstring_only_audit_drift=dict(file='normal_cut_handlebodies.py',tested=sha(old),current=current['normal_cut_handlebodies.py']),
            report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('source_sha256','docstring_only_audit_drift')}))
