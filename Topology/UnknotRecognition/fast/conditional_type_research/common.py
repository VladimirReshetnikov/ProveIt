"""Portable immutable archive loading and fresh replay dependency pins."""
from hashlib import sha256
import gzip
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
GROUPS = ('conditional-type-elimination', 'conditional-type-witnesses')


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(canonical_bytes(value)).hexdigest()


def _read(spec):
    stored = (PACKAGE/spec['path']).read_bytes()
    assert len(stored) == spec['stored_bytes']
    assert sha256(stored).hexdigest() == spec['stored_sha256']
    assert spec['encoding'] in ('gzip', 'identity')
    raw = gzip.decompress(stored) if spec['encoding'] == 'gzip' else stored
    assert len(raw) == spec['raw_bytes']
    assert sha256(raw).hexdigest() == spec['raw_sha256']
    return raw


def archive_bytes(group, name):
    manifest = json.loads((PACKAGE/'data/manifest.json').read_bytes())
    assert group in GROUPS
    entry = manifest['groups'][group]
    return _read(entry['original_manifest'] if name == 'manifest.json' else entry['files'][name])


def load_archive(group, name):
    raw = archive_bytes(group, name)
    return (json.loads(raw) if name.endswith('.json') else raw.decode()), raw


def staged_archive():
    manifest = json.loads((PACKAGE/'data/manifest.json').read_bytes())
    raw = _read(manifest['source_provenance'])
    return json.loads(raw), raw


def check_archive_bytes():
    """Check every exact historical byte against both manifest levels."""
    manifest = json.loads((PACKAGE/'data/manifest.json').read_bytes())
    assert manifest['schema'] == 'conditional-type-archives-v1'
    assert set(manifest['groups']) == set(GROUPS)
    count = 0
    for group in GROUPS:
        original, _ = load_archive(group, 'manifest.json')
        hashes = original.get('files_sha256') or {
            name: spec['sha256'] for name, spec in original['files'].items()}
        assert set(hashes) == set(manifest['groups'][group]['files'])
        assert len(hashes) == 8
        for name, expected in hashes.items():
            raw = archive_bytes(group, name)
            assert sha256(raw).hexdigest() == expected
            if 'files' in original:
                assert len(raw) == original['files'][name]['bytes']
            count += 1
    staged_archive()
    return dict(experiment_groups=2, original_manifest_files=2,
                preserved_group_files=count, staged_source_archives=1)


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*') if p.is_file()
              and '__pycache__' not in p.parts and p.suffix != '.pyc']
    paths.append(ROOT/'synthesis/conditional_type_matching.tex')
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_bytes(value)+b'\n')
