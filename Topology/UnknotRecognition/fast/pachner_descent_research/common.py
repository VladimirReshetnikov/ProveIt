"""Predeclared diagram inputs, whole-call controls, and complete source pins."""
from hashlib import sha256
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
ARMS = ('baseline', 'u1')
CASE_SPECS = (
    ('circle', None, ()),
    ('trefoil', 2, (1, 1, 1)),
    ('figure_eight', 3, (1, -2, 1, -2)),
    ('TT', 3, (1, 1, 1, 2, 2, 2)),
    ('T25', 2, (1, 1, 1, 1, 1)),
    ('T27', 2, (1, 1, 1, 1, 1, 1, 1)),
    ('W34', 3, (1, -2, 1, -2, 1, -2, 1, -2)),
)
BENCHMARK_PROTOCOL = dict(
    case_ids=['circle', 'trefoil', 'figure_eight', 'TT', 'T25'], arms=list(ARMS),
    warmups_per_arm=1, paired_rounds=3, aa_pairs=1, aa_arm='baseline',
    calls_per_case=10, total_calls=50,
    pair_order='baseline,u1 when (case_index+round_index)%2==0; reverse otherwise',
    wall_limit_seconds=None,
    timing_scope='Complete fresh recognition, independent proof/partial replay, canonical result serialization and SHA256; imports and prepared input PD outside.',
)
# Independent research accounting contract; no producer imports here.
CAP_STATS = {
    'max_sectors': ('sectors_attempted',),
    'max_bases': ('bases_attempted',),
    'max_crushes': ('crushing_steps', 'boundary_unlayerings', 'pachner32_moves', 'pachner_descent_macros'),
    'max_pivots': ('lp_pivots',),
    'max_anchors': ('anchors_tested',),
    'max_tree_nodes': ('nodes_attempted',),
    'max_hitting_subsets': ('hitting_subsets_tested',),
    'max_ellipsoid_iterations': ('lp_ellipsoid_iterations',),
    'max_feasibility_calls': ('lp_feasibility_calls',),
}
MAX_STATS = frozenset((
    'max_cached_sector_jobs', 'maximum_tableau_bits',
    'maximum_ellipsoid_precision', 'maximum_ellipsoid_dimension',
    'maximum_planned_ellipsoid_iterations', 'maximum_tree_depth',
    'maximum_transversal_size', 'maximum_conflict_size', 'peak_cached_conflicts',
))


def configs(arm):
    if arm not in ARMS:
        raise ValueError('unknown experimental arm')
    return dict(max_sectors=256, max_bases=10000, max_crushes=None,
        sector_order='diversified', sector_quantum=64, sector_method='transversal',
        max_pivots=10000, max_anchors=10000, lp_strategy='envelope',
        reduce_vertices=True, unlayer_boundary=True, reduce_pachner32=True,
        reduce_pachner_descent=arm == 'u1',
        max_tree_nodes=256, tree_model='source', max_hitting_subsets=10000,
        transversal_candidate_policy='conflicts', lp_policy='polynomial',
        lp_fast_path_pivots=None, max_ellipsoid_iterations=10000,
        max_feasibility_calls=10000)


def cases():
    from fastunknot.diagram import Diagram
    result = []
    for name, strands, word in CASE_SPECS:
        diagram = Diagram.from_pd([]) if strands is None else Diagram.from_braid(strands, word)
        result.append(dict(id=name, input_pd=[list(row) for row in diagram.pd],
            braid=None if strands is None else dict(strands=strands, word=list(word))))
    return result


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(canonical_bytes(value)).hexdigest()


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    # Archive replay uses independently retained STANDARD checking and the
    # older strict32 archive's authenticated source chains. Pin these actual
    # replay dependencies as well as the entire native/new research package.
    for directory in (PACKAGE, ROOT/'fast/strict_pachner32_research',
                      ROOT/'fast/conflict_composition_research'):
        paths += [p for p in directory.rglob('*') if p.is_file()
                  and '__pycache__' not in p.parts and p.suffix != '.pyc']
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_bytes(value)+b'\n')


def archive_bytes(group, name):
    """Return exact preserved bytes after both stored and raw hash checks."""
    import gzip
    manifest = json.loads((PACKAGE/'data/manifest.json').read_bytes())
    entry = manifest['groups'][group]
    spec = entry['original_manifest'] if name == 'manifest.json' else entry['files'][name]
    stored = (PACKAGE/spec['path']).read_bytes()
    assert len(stored) == spec['stored_bytes']
    assert sha256(stored).hexdigest() == spec['stored_sha256']
    raw = gzip.decompress(stored) if spec['encoding'] == 'gzip' else stored
    assert len(raw) == spec['raw_bytes'] and sha256(raw).hexdigest() == spec['raw_sha256']
    return raw


def load_archive(group, name):
    raw = archive_bytes(group, name)
    return (json.loads(raw) if name.endswith('.json') else raw.decode()), raw
