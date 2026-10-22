#!/usr/bin/env python3
"""Copy explicitly selected phase16 evidence/docs; never run a proof tool."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
P = Path('Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase16')
OWN = Path('/tmp/k215-phase16-root')
DOC = Path('/tmp/k215-phase16-docs')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(value):
    return (json.dumps(value, indent=2) + '\n').encode()

def read_json(path):
    return json.loads(path.read_bytes())

def check_current():
    review = read_json(OWN / 'current-review.json')
    assert len(review['sources']) == 199
    for name, row in review['sources'].items():
        assert sha(Path(row['current']).read_bytes()) == row['sha256'], name
    for row in read_json(OWN / 'adoption.json')['files']:
        path = ROOT / row['path']
        assert (sha(path.read_bytes()) if path.exists() else None) == row['after_sha256'], row['path']

check_current()
assert not (ROOT / P / 'lean').exists()
existing = {str(path.relative_to(ROOT)): sha(path.read_bytes())
            for path in (ROOT / P).rglob('*') if path.is_file()}
assert len(existing) == 26
copied = []

def put(source, target):
    source = Path(source)
    target = Path(target)
    assert not target.is_absolute() and '..' not in target.parts
    data = source.read_bytes()
    dest = ROOT / target
    assert not dest.exists(), str(target)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    assert dest.read_bytes() == data
    copied.append({'source': str(source), 'path': str(target), 'sha256': sha(data), 'bytes': len(data)})

core = ['README.md', 'basis-reference.json', 'basis.py', 'config.json', 'controls.py',
        'execution.tar.gz', 'freeze.json', 'index.json', 'packet.py', 'result.json', 'review.py']
published = Path('/tmp/k215-phase16-published-v2/lean')
assert {p.name for p in published.iterdir()} == set(core)
assert sha((published / 'freeze.json').read_bytes()) == 'aeb5ea38797a43131998ded29279a62a84be9581306cd8475f8a108bfcd1b211'
assert sha((published / 'execution.tar.gz').read_bytes()) == 'bca85a71e2d16e7e3cd2615d21d4ab4a1fe02700ae6b78e887046a221d799377'
for name in core:
    put(published / name, P / 'lean' / name)

actual = ['capture-outer.json', 'capture.stderr', 'capture.stdout',
          'capture2-outer.json', 'capture2.json', 'capture2.stderr', 'capture2.stdout',
          'capture3-outer.json', 'capture3.json', 'capture3.stderr', 'capture3.stdout',
          'controls.json', 'controls.stderr', 'controls.stdout',
          'saved-owner-outer.json', 'saved-owner.stderr', 'saved-owner.stdout',
          'saved-owner2-outer.json', 'saved-owner2.json', 'saved-owner2.stderr', 'saved-owner2.stdout']
for name in actual:
    put(Path('/tmp/k215-phase16-publication-execution') / name, P / 'lean/actual' / name)

peer = ['copy-map.json', 'core-after.json', 'core-before.json', 'outer.json',
        'predecessor-held-review.json', 'review.json', 'run_saved_once.predecessor-unexecuted.py',
        'run_saved_once.py', 'saved.json', 'saved.stderr', 'saved.stdout', 'source-review.json']
for name in peer:
    put(Path('/tmp/k215-phase16-saved-peer') / name, P / 'lean/independent' / name)
receipt = (ROOT / P / 'lean/actual/saved-owner2.json').read_bytes()
assert receipt == (ROOT / P / 'lean/independent/saved.json').read_bytes()
assert sha(receipt) == 'd27d60176c659c363b99dca255ab9d7b622dbdd6b07624008205d8b65680c5f0'
for name in core + ['failure.json', 'saved-owner-outer.json', 'saved-owner.stderr', 'saved-owner.stdout']:
    put(Path('/tmp/k215-phase16-publication/history/saved1-json-comparison') / name,
        P / 'lean/history/saved1-json-comparison' / name)
put(OWN / 'history-publication.md', P / 'lean/history/README.md')
put('/tmp/k215-phase16-adoption-peer/review.json', P / 'integration/independent-adoption-review.json')

coordination = ['attributed-proposal-build.txt', 'build-evidence.json', 'findings.txt',
                'mapping.json', 'newer-lean-commits.txt', 'quotient-eight-files.diff', 'review.py']
for name in coordination:
    put(Path('/tmp/k215-phase16-coordination') / name, P / 'coordination' / name)
put(OWN / 'coordination.md', P / 'coordination/README.md')

mapping = read_json(DOC / 'copy-map.json')
assert mapping['file_count'] == len(mapping['files']) == 7
put(DOC / 'copy-map.json', P / 'documentation/history/before-saved/copy-map.json')
overview = next(row for row in mapping['files'] if row['target'] == str(P / 'README.md'))
put(overview['source'], P / 'documentation/history/before-saved/README.md')
old = ('**Saved evidence package:** publication of the runtime evidence packet is pending.\n'
       'Its saved-reader checks and publication will be recorded here separately from the\n'
       'accepted actual results and exact source adoption above.\n')
new = ('The [saved Lean evidence packet](lean/README.md) passes capture, owner review and\n'
       '[independent saved review](lean/independent/review.json), including the binding to\n'
       'all 199 current project sources. Its archive has 487 members and 1,192,362 bytes.\n'
       'Both saved reads produce the identical receipt SHA-256\n'
       '`d27d60176c659c363b99dca255ab9d7b622dbdd6b07624008205d8b65680c5f0`.\n'
       '[Adoption](integration/adoption.json), [current source bindings](integration/current-review.json)\n'
       'and [concurrent-work review](coordination/README.md) are saved alongside it.\n'
       'Two metadata-packaging failures and their exact predecessors remain\n'
       '[separate history](lean/history/README.md); neither is a compiler failure.\n')
text = Path(overview['source']).read_text()
assert text.count(old) == 1
Path(overview['source']).write_text(text.replace(old, new))
overview['sha256'] = sha(Path(overview['source']).read_bytes())
overview['bytes'] = Path(overview['source']).stat().st_size
mapping['status'] = 'FINAL_SEVEN_DOCS_WITH_PASS_SAVED_EVIDENCE'
mapping['pending'] = []
mapping['saved_receipt_sha256'] = sha(receipt)
mapping['canonical_writes'] = True
for row in mapping['files']:
    src = Path(row['source'])
    dest = ROOT / row['target']
    data = src.read_bytes()
    assert sha(data) == row['sha256'] and len(data) == row['bytes']
    assert (sha(dest.read_bytes()) if dest.exists() else None) == row['before_sha256'], row['target']
    if dest.exists():
        put(dest, P / 'documentation/before' / row['target'])
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    copied.append({'source': str(src), 'path': row['target'], 'sha256': sha(data),
                   'bytes': len(data), 'before_sha256': row['before_sha256']})
(DOC / 'copy-map.json').write_bytes(dump(mapping))
put(DOC / 'copy-map.json', P / 'documentation/copy-map.json')
put(DOC / 'documentation.diff', P / 'documentation/history/before-saved/documentation.diff')
put(DOC / 'draft-review.json', P / 'documentation/history/before-saved/draft-review.json')
put(OWN / 'finish_publication.py', P / 'integration/finish_publication.py')
check_current()
for rel, digest in existing.items():
    assert sha((ROOT / rel).read_bytes()) == digest, rel
for row in copied:
    assert sha((ROOT / row['path']).read_bytes()) == row['sha256'], row['path']
record = {'status': 'PASS_EXACT_PACKET_AND_DOCUMENTATION_COPY',
          'proof_execution': False, 'saved_reader_rerun': False,
          'current_project_sources_checked': 199, 'existing_phase16_files': existing,
          'files': copied, 'receipt_sha256': sha(receipt),
          'archive_sha256': sha((published / 'execution.tar.gz').read_bytes()),
          'preserves_other_main': '140d832128fd43873f16e385766cd3cee08df8a9'}
result = ROOT / P / 'integration/publication-copy-map.json'
result.write_bytes(dump(record))
owned = set(existing) | {row['path'] for row in copied if row['path'].startswith(str(P) + '/')} | {str(result.relative_to(ROOT))}
actual_owned = {str(q.relative_to(ROOT)) for q in (ROOT / P).rglob('*') if q.is_file()}
assert actual_owned == owned, sorted(actual_owned ^ owned)
print(json.dumps({'status': record['status'], 'phase16_files': len(owned),
                  'copy_actions': len(copied), 'map_sha256': sha(result.read_bytes())}))
