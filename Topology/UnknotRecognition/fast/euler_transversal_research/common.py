"""Source pins and fixed correctness-audit configuration; no timing policy."""
from hashlib import sha256
import json
from pathlib import Path

from euler_tree_research.benchmark import ROOT, source_hashes as inherited_hashes

PACKAGE = Path(__file__).resolve().parent
STRATEGIES = ('envelope', 'anchors')
DIAGRAM_CONFIG = dict(sector_method='transversal', tree_model='source',
    lp_strategy='envelope', reduce_vertices=True, max_tree_nodes=256,
    max_pivots=10000, max_anchors=10000, max_hitting_subsets=10000,
    max_crushes=None)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    # The inherited map includes the entire native Python package and the
    # research dependencies used for the fresh original-standard comparisons.
    result = inherited_hashes()
    for path in sorted(PACKAGE.rglob('*')):
        if path.is_file() and path.suffix in ('.py', '.md', '.json'):
            name = 'fast/euler_transversal_research/'+str(path.relative_to(PACKAGE))
            result[name] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))


def lower_fixtures():
    return json.loads((PACKAGE/'data/lower_witnesses.json').read_text())['records']
