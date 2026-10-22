"""Adopt the exact, independently checked phase14 overlay and two retirements."""
from pathlib import Path
import hashlib, json

R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
S = Path('/tmp/k215-phase14-check')
P = R / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14'
read = lambda p: json.loads(Path(p).read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert read('/tmp/k215-phase14-root/root-actual-review.json')['status'] == 'PASS_ROOT_RAW_PHASE14_ACTUAL'
sources = read(S / 'sources.json')
assert len(sources) == 7
baseline = read('/tmp/k215-phase13-root/current-review.json')['sources']
retirements = read(S / 'producer-boundary.json')['proposed_retirements']
assert len(retirements) == 2
writes, deletions = [], []
for row in sources:
    current = Path(baseline[row['module']]['current'])
    assert sha(current) == baseline[row['module']]['sha256']
    assert sha(row['source']) == row['source_sha256']
    writes.append((current, Path(row['source'])))
for row in retirements:
    current = Path(row['canonical'])
    assert sha(current) == row['before_sha256'] == sha(row['before_snapshot'])
    deletions.append(current)
assert len(set(p for p, _ in writes) | set(deletions)) == 9
for path, digest in read(S / 'producer-boundary.json')['accepted_five_files'].items():
    assert sha(path) == digest
assert not P.exists()
records = []
before_bytes = after_bytes = before_lines = after_lines = 0
for current, candidate in writes + [(p, None) for p in deletions]:
    relative = current.relative_to(R)
    before = current.read_bytes()
    after = candidate.read_bytes() if candidate else None
    archived = P / 'integration/before' / relative
    archived.parent.mkdir(parents=True, exist_ok=True)
    archived.write_bytes(before)
    records.append({'path': str(relative), 'before_sha256': sha(current),
                    'after_sha256': sha(candidate) if candidate else None,
                    'before_snapshot': str(archived.relative_to(R)),
                    'candidate': str(candidate) if candidate else None,
                    'action': 'replace' if candidate else 'retire'})
    before_bytes += len(before); before_lines += len(before.splitlines())
    if after is not None:
        after_bytes += len(after); after_lines += len(after.splitlines())
for current, candidate in writes:
    current.write_bytes(candidate.read_bytes())
for current in deletions:
    current.unlink()
for row in records:
    current = R / row['path']
    if row['action'] == 'replace':
        assert sha(current) == row['after_sha256']
    else:
        assert not current.exists() and not current.is_symlink()
record = {'status': 'ADOPTED_EXACT_CHECKED_PHASE14', 'files': records,
          'source_writes': 7, 'retirements': 2,
          'before_bytes': before_bytes, 'after_bytes': after_bytes,
          'bytes_saved': before_bytes - after_bytes,
          'before_lines': before_lines, 'after_lines': after_lines,
          'lines_saved': before_lines - after_lines,
          'scope': 'Seven compiled Lean replacements and two separately checked retirements; machine, endpoints and prior five adoptions unchanged.'}
(P / 'integration/adoption.json').write_text(json.dumps(record, indent=2) + '\n')
Path('/tmp/k215-phase14-root/adoption.json').write_text(json.dumps(record, indent=2) + '\n')
print('ADOPTED', record['bytes_saved'], 'bytes;', record['lines_saved'], 'lines')
