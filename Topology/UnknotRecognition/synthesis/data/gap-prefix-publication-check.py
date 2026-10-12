"""Bind published gap-prefix evidence to the current source and retained baseline."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).parent
sys.path.insert(0, str(ROOT/'fast'))
from normal_orbit_research.seeds import sources
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((DATA/(name+'.json')).read_text())
benchmark = read('gap-prefix-benchmark')
audit = read('gap-prefix-audit')
probe = read('gap-prefix-pivot-width-probe')
expected = {str(p.relative_to(ROOT/'fast')):sha(p) for p in (ROOT/'fast/fastunknot').rglob('*.py')}
assert benchmark['native_source_sha256'] == audit['native_source_sha256'] == expected
assert probe['native_source_sha256'] == sources()
assert benchmark['driver_sha256'] == sha(DATA/'gap-prefix-benchmark-driver.py')
assert audit['driver_sha256'] == sha(DATA/'gap-prefix-experiment.py')
assert audit['completed_prefix_driver_sha256'] == benchmark['driver_sha256']
assert probe['driver_sha256'] == sha(DATA/'gap-prefix-pivot-width-probe.py')
base = DATA/'gap-prefix-baseline'
assert benchmark['baseline_sha256'] == audit['baseline_sha256'] == {p.name:sha(p) for p in base.glob('*.py')}
for p in base.glob('*.py'):
    original = subprocess.check_output(['git','show',
        'd9456c5bdb94820bfa9e480e9ed73c10a769e59a:Topology/UnknotRecognition/fast/fastunknot/'+p.name])
    assert p.read_bytes() == original
changed = subprocess.check_output(['git','diff','--name-only',
    'd9456c5bdb94820bfa9e480e9ed73c10a769e59a','--','Topology/UnknotRecognition/fast/fastunknot'],
    cwd=ROOT.parents[1], text=True).splitlines()
assert {Path(p).name for p in changed} == {p.name for p in base.glob('*.py')}
paths = [ROOT/'fast/marked_parallelity_research'/n for n in ('corpus.json','three_handle_corpus.json')]
assert benchmark['corpus_sha256'] == audit['corpus_sha256'] == {p.name:sha(p) for p in paths}
bank = {c['id']:c for p in paths for c in json.loads(p.read_text())['cases']}
assert audit['finished'] and len(audit['cases']) == 120
assert {c['id'] for c in audit['cases']} == set(bank)
assert Counter(c['status'] for c in audit['cases']) == {'COMPLETE':111,'INCONCLUSIVE':9}
assert all(c['identical_certificate'] for c in audit['cases'])
assert benchmark['finished'] and len(benchmark['cases']) == 11
for c in benchmark['cases']:
    assert c['identical_certificate'] and c['status'] == 'COMPLETE'
    assert len(c['samples']) == 5 and len(c['aa_samples']) == 3
    for arm in ('before','after'):
        assert c[arm+'_median'] == statistics.median(s[arm]['total'] for s in c['samples'])
    for field,measurement in (('paired_speedup','total'),('replay_speedup','replay')):
        assert c[field] == statistics.median(s['before'][measurement]/s['after'][measurement] for s in c['samples'])
    assert c['aa_median'] == statistics.median(s['ratio'] for s in c['aa_samples'])
    if c['id'] in bank:
        assert c['proof_sha256'] == next(a['proof_sha256'] for a in audit['cases'] if a['id']==c['id'])
assert probe['counts'] == {'matrix_plans':120,'full_prepeeling':118,'nonzero_residual_optima':2}
assert probe['delivered_source_sha256'] == {str(p.relative_to(ROOT/'reports/110')):sha(p)
                                          for p in (ROOT/'reports/110/pivotwidth').glob('*.py')}
# Only the independent matching checker is loaded; no optimizer is imported.
spec = importlib.util.spec_from_file_location('_pivot110_checker', ROOT/'reports/110/pivotwidth/verify.py')
checker = importlib.util.module_from_spec(spec); spec.loader.exec_module(checker)
for c in probe['cases']:
    source = bank[c['id']]
    prepared = _prepare(source['triangulation'], lambda:None)
    g = _reference_parallelity(prepared, _coordinates(prepared,source['coordinates'],lambda:None), lambda:None)
    reduced, top = reduce_core_three_handles(g, strategy='max_weight')
    assert replay_core_three_handles(g, top) == reduced
    core = reduced['core']; columns = [h['id'] for h in core['handles1']]
    rows = [Counter(f['handle'] for f in h['cycle'] if f['dimension']==1) for h in core['handles2']]
    matrix = [[r.get(col,0) for col in columns] for r in rows]
    checked = checker.replay(matrix,[1]*len(rows),c['plan'],columns=len(columns))
    assert checked['valid'] and c['rows']==len(rows) and c['columns']==len(columns)
    if c['residual_rows']:
        assert c['matrix']==matrix and c['top_certificate']==json.loads(json.dumps(top))
        assert c['exhaustive_optimum']==c['plan']['deferred_weight']==1
        # Prove nonzero deferral by exhibiting the nonempty full-peeling residual.
        live = set(range(len(rows)))
        while live:
            col = next((col for col in columns if sum(rows[r].get(col,0) for r in live)==1), None)
            if col is None: break
            live.remove(next(r for r in live if rows[r].get(col,0)))
        assert len(live)==c['residual_rows'] and live
        assert all(sum(rows[r].get(col,0) for r in live)!=1 for col in columns)
        # The accepted one-row-deferral plan supplies the matching upper bound.
    else:
        assert c['plan']['deferred_weight']==0 and c['plan']['stats']['peak_states']==0
log = (DATA/'gap-prefix-tests.txt').read_text()
match = re.search(r'Ran (\d+) tests in ([\d.]+)s\n\nFAILED \(errors=1, skipped=13\)',log)
assert match and int(match[1]) == 1737
rerun = (DATA/'gap-prefix-regina-rerun.txt').read_text()
rerun_match = re.search(r'Ran 14 tests in ([\d.]+)s\n\nOK\n',rerun)
assert rerun_match and 'skipped=' not in rerun
needed = []
for line in log.splitlines():
    if line.endswith(' ... ERROR') or ' ... skipped ' in line:
        m = re.match(r'(test_\w+) \(([^)]+)\)',line); assert m
        needed.append(m[2] if m[2].endswith('.'+m[1]) else m[2]+'.'+m[1])
assert len(needed) == 14 and read('gap-prefix-regina-rerun')['tests'] == needed
for name in needed:
    assert '('+name+') ... ok' in rerun
assert 'ModuleNotFoundError: No module named \'regina\'' in log
assert 'Ran 8 tests in 0.218s\n\nOK' in (DATA/'gap-prefix-focused.txt').read_text()
assert 'Ran 52 tests in 0.491s\n\nOK' in (DATA/'gap-prefix-report110-tests.txt').read_text()
artifacts = sorted(p for p in DATA.glob('gap-prefix-*') if p.is_file() and p!=Path(__file__).with_suffix('.json'))
result = dict(scope='Local exact gap-mapping improvement; general quasi-polynomial recognition remains unproved',
              sources_match=True,covered_test_methods=int(match[1]),broad_test_seconds=float(match[2]),
              broad_passed=1723,broad_missing_dependency_error=1,broad_dependency_skips=13,
              dependency_rerun_passed=14,dependency_rerun_seconds=float(rerun_match[1]),
              native_cuts=120,unchanged_positive_certificates=111,unchanged_inconclusive=9,
              benchmark_cases=11,source_matrix_plans=120,nonzero_residual_optima=2,
              artifact_sha256={p.name:sha(p) for p in artifacts},
              report_pdf_sha256=sha(ROOT/'synthesis/report.pdf'))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('Publication checks pass: 1737 methods covered across broad run and dependency rerun, 111 unchanged certificates, 120 independently replayed matrix plans.')
