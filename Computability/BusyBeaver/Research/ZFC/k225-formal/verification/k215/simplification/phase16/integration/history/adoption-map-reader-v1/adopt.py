"""Adopt only the exact checked quotient overlay and its recorded producer retirement."""
from pathlib import Path
import hashlib, json

R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
S = Path(__file__).resolve().parent
Q = Path('/tmp/k215-phase16-quotient')
D = Path('/tmp/k215-phase16-check')
P = R / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase16'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
save = lambda p, x: p.write_text(json.dumps(x, indent=2) + '\n')

assert read(S / 'actual-review.json')['status'] == 'PASS_INDEPENDENT_ACTUAL_RECORD_REVIEW'
for scope in ['primary-run1', 'compatibility-run1']:
    assert sha(D / scope / 'result.json') == read(S / 'actual-review.json')['scopes'][scope]['result_sha256']
freeze = Q / 'final-source-freeze.json'
assert sha(freeze) == 'd6905d22aeba74d7481922267f84b1c31d7590c63907a24a26039bf10ad9d085'
for item in read(freeze)['files']:
    assert sha(item['path']) == item['sha256']
rows = read(Q / 'sources.json')
assert len(rows) == 13 and len({r['target'] for r in rows}) == 13
baseline = read('/tmp/k215-phase15-root/current-review.json')['sources']
assert len(baseline) == 199
for row in baseline.values():
    assert sha(row['current']) == row['sha256']
retirement = read(Q / 'retirement.json')
assert retirement['path'].endswith('/generate_kq1.py')
assert sha(R / retirement['path']) == retirement['before_sha256']
for row in rows:
    assert sha(R / row['target']) == row['before_sha256']
    assert sha(row['source']) == row['source_sha256']
    assert sha(row['before_snapshot']) == row['before_sha256']
assert not P.exists()
(P / 'integration/before').mkdir(parents=True)
changes = []
for row in rows:
    target = R / row['target']
    before = P / 'integration/before' / row['target']
    before.parent.mkdir(parents=True, exist_ok=True)
    before.write_bytes(target.read_bytes())
    assert sha(before) == row['before_sha256']
    target.write_bytes(Path(row['source']).read_bytes())
    assert sha(target) == row['source_sha256']
    changes.append({'path': row['target'], 'action': 'write',
                    'before_sha256': row['before_sha256'], 'after_sha256': row['source_sha256'],
                    'before_snapshot': str(before.relative_to(R)), 'candidate': row['source']})
target = R / retirement['path']
before = P / 'integration/before' / retirement['path']
before.parent.mkdir(parents=True, exist_ok=True)
before.write_bytes(target.read_bytes())
assert sha(before) == retirement['before_sha256']
target.unlink()
assert not target.exists() and not target.is_symlink()
changes.append({'path': retirement['path'], 'action': 'retire',
                'before_sha256': retirement['before_sha256'], 'after_sha256': None,
                'before_snapshot': str(before.relative_to(R)), 'candidate': None})
adoption = {'status': 'ADOPTED_EXACT_CHECKED_PHASE16_QUOTIENT_SUCCESSOR', 'files': changes,
            'source_freeze_sha256': sha(freeze), 'metrics': read(freeze)['metrics'],
            'actual_review_sha256': sha(S / 'actual-review.json')}
save(P / 'integration/adoption.json', adoption)
expected = {r['module']: r['source_sha256'] for r in rows}
sources = {m: {'current': r['current'], 'sha256': expected.get(m, r['sha256'])} for m, r in baseline.items()}
for row in sources.values():
    assert sha(row['current']) == row['sha256']
absent = read('/tmp/k215-phase15-root/current-review.json')['prior_four_absences_retained']
absent = absent + [str(target)]
for path in absent:
    assert not Path(path).exists() and not Path(path).is_symlink()
current = {'status': 'PASS_CURRENT_PHASE16_ADOPTION', 'project_sources': 199,
           'canonical_writes': 13, 'retirements': 1, 'sources': sources,
           'retained_absences': absent,
           'historical_before_sources': [{k: r[k] for k in ['path', 'before_sha256', 'before_snapshot']} for r in changes],
           'adoption_sha256': sha(P / 'integration/adoption.json')}
save(P / 'integration/current-review.json', current)
save(S / 'adoption.json', adoption)
save(S / 'current-review.json', current)
print(current['status'], '13 writes, one producer retirement; 199 project source hashes bound')
