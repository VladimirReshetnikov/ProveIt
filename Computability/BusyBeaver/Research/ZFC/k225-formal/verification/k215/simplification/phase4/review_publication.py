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
parser.add_argument('--repo', type=Path)
args = parser.parse_args()
repo = args.repo.resolve() if args.repo else next(p for p in Path(__file__).resolve().parents if (p / 'lean-toolchain').is_file())
root = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'
sha = lambda data: hashlib.sha256(data).hexdigest()
archives = []
for packet in ['phase4']:
    for archive in sorted((root / packet).rglob('*.tar.gz')):
        if archive.name == 'portable-control.tar.gz':
            record = json.loads((archive.parent / 'portable-control.json').read_text())
            assert sha(archive.read_bytes()) == record['control_archive_sha256']
            with tarfile.open(archive, 'r:gz') as tar:
                raw_index = tar.extractfile('index.json').read()
            index = json.loads(raw_index)
            expected = {p: h['sha256'] for p, h in index.items()}
            expected['index.json'] = sha(raw_index)
        elif (archive.parent / 'execution-index.json').exists():
            index = json.loads((archive.parent / 'execution-index.json').read_text())
            expected = {p: h if isinstance(h, str) else h['sha256'] for p, h in index.items()}
        elif (archive.parent / 'index.json').exists():
            index = json.loads((archive.parent / 'index.json').read_text())
            expected = {p: h if isinstance(h, str) else h['sha256'] for p, h in index.items()}
        elif (archive.parent / 'evidence-index.json').exists():
            index = json.loads((archive.parent / 'evidence-index.json').read_text())
            assert sha(archive.read_bytes()) == index['archive_sha256']
            expected = {e['path']: e['sha256'] for e in index['members']}
        else:
            raise AssertionError(('Missing archive index', archive))
        actual = {}
        with tarfile.open(archive, 'r:gz') as tar:
            for entry in tar:
                assert entry.isfile(), (archive, entry.name, 'nonfile member')
                path = PurePosixPath(entry.name)
                assert not path.is_absolute() and '..' not in path.parts
                assert not set(path.suffixes) & {'.olean', '.ilean', '.vo', '.vos', '.vok', '.pyc', '.o', '.so', '.a'}
                assert entry.name not in actual
                actual[entry.name] = sha(tar.extractfile(entry).read())
        assert actual == expected, (archive, 'member hash mismatch')
        archives.append({'path': str(archive.relative_to(repo)), 'sha256': sha(archive.read_bytes()),
                         'members': len(actual)})
links = []
for packet in ['phase4']:
    for doc in sorted((root / packet).rglob('README.md')):
        for target in re.findall(r'(?<!!)\[[^\]]*\]\(([^)]+)\)', doc.read_text()):
            target = target.strip('<>')
            if '://' in target or target.startswith('#'):
                continue
            path = (doc.parent / unquote(target.split('#', 1)[0])).resolve()
            if not path.exists():
                raise AssertionError(('Broken link', doc, target, path))
            links.append({'document': str(doc.relative_to(repo)), 'target': target})
result = {'status': 'PASS', 'archives': archives,
          'links_checked': len(links),
          'script_sha256': sha(Path(__file__).read_bytes()),
          'scope': 'Saved archive bytes, safe member sets, exact indexed hashes, '
                   'and local README targets; not a proof-kernel replay.'}
args.out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'archives': len(archives),
                  'members': sum(e['members'] for e in archives),
                  'links': len(links)}))
