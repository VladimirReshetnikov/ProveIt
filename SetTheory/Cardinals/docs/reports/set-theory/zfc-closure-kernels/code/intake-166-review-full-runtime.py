"""Own metadata-only review of the root's completed replay; no supplied imports."""
from pathlib import Path
import hashlib, json

W = Path('/tmp/zfc244-248bc05936-inspection/intake')
P = W.parent / 'zfc244-compensated-routing-20261018'
F = Path('/tmp/zfc244-root-replays/full-runtime')
checks = []
def ck(c, text):
    if not c: raise AssertionError(text)
    checks.append(text)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p): return {'path': str(p), 'sha256': sha(p)}
e = json.loads((F / 'execution.json').read_text())
fresh = json.loads((F / 'verification.json').read_text())
delivered = json.loads((P / 'runtime/candidate_1_full_symbolic.json').read_text())
ck(e['returncode'] == 0 and not e['timed_out'] and e['semantic_postchecks'] == 'PASS', 'terminal root success')
ck(e['process_group_limit_seconds'] == 600 and 0 < e['wall_seconds'] < 600, 'within actual original bound')
ck(e['command'][1:] == ['-B', 'runtime/code/full_symbolic_parametric.py', '--table', 'runtime/candidate_1_244_old.tm', '--all-values', '--sites', 'runtime/certificate/sites_physical.json', '--output', str(F / 'verification.json')], 'full unbounded-parameter command; no case limit')
ck(Path(e['cwd']) == F / 'package', 'disposable copy cwd')
ck(e['result_sha256'] == sha(F / 'verification.json') == '18bed1d3a3ccb75eac3686d0a68028c20e248ffc4350e6cc674d01c35e8c75a0', 'exact fresh result')
ck(fresh['status'] == 'PASS' and fresh['complete'] is True and fresh['positive_progress_checked'] is True, 'complete positive-progress result')
ck(fresh['counts'] == {'cases': 8391, 'symbolic_rules': 2315075} and len(fresh['rows']) == 488 and fresh['minimum_steps'] == 13, 'exact cases/rules/rows/minimum')
ck({k: v for k, v in fresh.items() if k != 'seconds'} == {k: v for k, v in delivered.items() if k != 'seconds'}, 'all complete certificate fields identical except elapsed time')
ck((F / 'stderr.log').read_bytes() == b'', 'empty raw stderr')
ck(bool((F / 'stdout.log').read_bytes()), 'nonempty raw stdout retained')
plan = json.loads((W / 'placement-proposal.json').read_text())
expected = set()
for row in plan['files']:
    rel = row['relative']
    ck(sha(P / rel) == row['sha256'], 'untouched original ' + rel)
    if rel == 'SHA256SUMS':
        ck(not (F / 'package' / rel).exists(), 'only delivery checksum manifest omitted on copy')
    else:
        ck((F / 'package' / rel).read_bytes() == (P / rel).read_bytes(), 'exact executed-copy bytes ' + rel)
        expected.add(rel)
ck({str(p.relative_to(F / 'package')) for p in (F / 'package').rglob('*') if p.is_file()} == expected, 'complete190-member executed-copy census')
result = {
    'status': 'EXISTING_FULL_RUNTIME_EVIDENCE_REVIEW_PASS', 'findings': [],
    'reviewer_role': 'Intake/helper author reviewing existing root execution metadata; no supplied verifier, simulator, compiler or builder executed by reviewer.',
    'execution': d(F / 'execution.json'), 'result': d(F / 'verification.json'),
    'stdout': d(F / 'stdout.log'), 'stderr': d(F / 'stderr.log'),
    'delivered_certificate': d(P / 'runtime/candidate_1_full_symbolic.json'),
    'root_runner': d(Path('/tmp/zfc244-root-replays/run_replays.py')),
    'reviewer_source': d(Path(__file__)), 'wall_seconds': e['wall_seconds'],
    'scope': 'Exact completed principal all-values replay, all certificate fields except seconds and all190 copied files. This is existing-output review, not another independently implemented symbolic checker or a Lean/PA theorem. Variants2/3 full runs remain inherited.',
    'supersession': 'Initial dossier/map v1 used the previous running status; they remain immutable. Terminal evidence is used only in separately named v2 prose/map.',
    'checks': checks,
}
out = W / 'full-runtime-evidence-review.json'
with out.open('x') as stream: stream.write(json.dumps(result, indent=2) + '\n')
print(sha(out), len(checks))
