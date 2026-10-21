"""Read-only review of the simplification evidence packets."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import tarfile
from urllib.parse import unquote

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, required=True)
parser.add_argument('--allow-pending-phase2-lean', action='store_true')
args = parser.parse_args()
repo = Path('/home/codex/.codex/worktrees/ec20/Proofs')
root = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'
sha = lambda data: hashlib.sha256(data).hexdigest()
archives = []
manifests = []
for name in ['enum-contracts/publication.json', 'phase2/source-symmetry/index.json',
             'phase2/rho8-global/lean/publication.json']:
    manifest = root / name
    entries = json.loads(manifest.read_text())['files']
    expected = entries if isinstance(entries, dict) else {e['path']: e['sha256'] for e in entries}
    for path, expected_hash in expected.items():
        assert not PurePosixPath(path).is_absolute() and '..' not in PurePosixPath(path).parts
        assert sha((manifest.parent / path).read_bytes()) == expected_hash, (manifest, path)
    manifests.append({'path': str(manifest.relative_to(repo)), 'sha256': sha(manifest.read_bytes()),
                      'files': len(expected)})
for packet in ['phase2', 'phase3']:
    for archive in sorted((root / packet).rglob('*.tar.gz')):
        if (archive.parent / 'execution-index.json').exists():
            index = json.loads((archive.parent / 'execution-index.json').read_text())
            expected = {p: h if isinstance(h, str) else h['sha256'] for p, h in index.items()}
        elif (archive.parent / 'index.json').exists():
            index = json.loads((archive.parent / 'index.json').read_text())
            expected = {p: h if isinstance(h, str) else h['sha256'] for p, h in index.items()}
        elif (archive.parent / 'evidence-index.json').exists():
            index = json.loads((archive.parent / 'evidence-index.json').read_text())
            assert sha(archive.read_bytes()) == index['archive_sha256']
            expected = {e['path']: e['sha256'] for e in index['files']}
        else:
            raise AssertionError(('Missing archive index', archive))
        actual = {}
        with tarfile.open(archive, 'r:gz') as tar:
            for entry in tar:
                assert entry.isfile(), (archive, entry.name, 'nonfile member')
                path = PurePosixPath(entry.name)
                assert not path.is_absolute() and '..' not in path.parts
                assert path.suffix not in {'.olean', '.ilean', '.vo', '.vos', '.vok', '.pyc'}
                assert entry.name not in actual
                actual[entry.name] = sha(tar.extractfile(entry).read())
        assert actual == expected, (archive, 'member hash mismatch')
        archives.append({'path': str(archive.relative_to(repo)), 'sha256': sha(archive.read_bytes()),
                         'members': len(actual)})
links = []
pending = []
for packet in ['phase2', 'phase3', 'enum-contracts']:
    for doc in sorted((root / packet).rglob('README.md')):
        for target in re.findall(r'(?<!!)\[[^\]]*\]\(([^)]+)\)', doc.read_text()):
            target = target.strip('<>')
            if '://' in target or target.startswith('#'):
                continue
            path = (doc.parent / unquote(target.split('#', 1)[0])).resolve()
            if not path.exists():
                if (args.allow_pending_phase2_lean and path == root / 'phase2/lean/README.md'):
                    pending.append({'document': str(doc.relative_to(repo)), 'target': target})
                    continue
                raise AssertionError(('Broken link', doc, target, path))
            links.append({'document': str(doc.relative_to(repo)), 'target': target})
result = {'status': 'PASS_WITH_EXPLICIT_PENDING_LINKS' if pending else 'PASS',
          'archives': archives, 'manifests': manifests,
          'links_checked': len(links), 'pending_links': pending,
          'script_sha256': sha(Path(__file__).read_bytes()),
          'scope': 'Saved archive bytes, safe member sets, exact indexed hashes, '
                   'and local README targets; not a proof-kernel replay.'}
args.out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'archives': len(archives),
                  'members': sum(e['members'] for e in archives),
                  'links': len(links), 'pending_links': len(pending)}))
