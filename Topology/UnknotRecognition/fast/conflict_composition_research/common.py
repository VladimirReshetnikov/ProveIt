"""Immutable original inputs, historical discovery pins, and fresh replay pins."""
from hashlib import sha256
import gzip
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def load(name):
    path = PACKAGE/'data'/name
    raw = path.read_bytes()
    if path.suffix == '.gz':
        raw = gzip.decompress(raw)
    return json.loads(raw)


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*') if p.is_file()
              and '__pycache__' not in p.parts and p.suffix != '.pyc']
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def verify_provenance():
    result = load('provenance.json')
    assert result['schema'] == 'conflict-composition-generation-v1'
    for relative, item in result['inputs'].items():
        raw = (PACKAGE/relative).read_bytes()
        assert sha256(raw).hexdigest() == item['retained_sha256']
        if item['compression'] == 'gzip':
            raw = gzip.decompress(raw)
        else:
            assert item['compression'] is None
        assert len(raw) == item['original_bytes']
        assert sha256(raw).hexdigest() == item['original_sha256']
    return result
