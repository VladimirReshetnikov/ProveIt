"""Immutable fixtures, historical discovery provenance, and fresh replay pins."""
from hashlib import sha256
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def load(name):
    return json.loads((PACKAGE/'data'/name).read_text())


def source_hashes():
    """Pin every native Python file and every immutable package input/source."""
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*')
              if p.is_file() and p.suffix in ('.py', '.md', '.json', '.txt')]
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def verify_generation_provenance():
    provenance = load('provenance.json')
    assert provenance['schema'] == 'boundary-transversal-generation-provenance-v1'
    for relative, record in provenance['inputs'].items():
        assert sha256((PACKAGE/relative).read_bytes()).hexdigest() == record['sha256']
    fixtures = load('lower_witnesses.json')
    historical = load('provenance/layer-refuter.json')
    assert historical['source_sha256']['fast/euler_transversal_research/data/lower_witnesses.json'] == \
        provenance['inputs']['data/lower_witnesses.json']['sha256']
    for record in fixtures['records']:
        assert digest(record['source']) == record['source_sha256']
    return provenance
