"""Predeclared genuine inputs, identical controls, and complete source pins."""
from hashlib import sha256
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
ARMS = ('raw', 'factored')
CASE_SPECS = (
    ('circle', None, ()),
    ('trefoil', 2, (1, 1, 1)),
    ('figure_eight', 3, (1, -2, 1, -2)),
    ('UU', 3, (1, 2)),
    ('UT', 3, (1, 2, 2, 2)),
    ('TT', 3, (1, 1, 1, 2, 2, 2)),
    ('TF', 4, (1, 1, 1, 2, -3, 2, -3)),
    ('FF', 5, (1, -2, 1, -2, 3, -4, 3, -4)),
)
BENCHMARK_PROTOCOL = dict(
    case_ids=['circle', 'trefoil', 'figure_eight', 'UU', 'UT'],
    arms=list(ARMS), warmups_per_arm=1, paired_rounds=3, aa_pairs=1,
    aa_arm='raw', calls_per_case=10, total_calls=50,
    pair_order='raw,factored when (case_index+round_index)%2==0; reverse otherwise',
    wall_limit_seconds=None,
    timing_scope='Complete fresh recognition, independent proof/partial replay, canonical result serialization and SHA256; imports and prepared input PD outside.',
)
# Independent research accounting contract; no producer imports here.
CAP_STATS = {
    'max_sectors': ('sectors_attempted',),
    'max_bases': ('bases_attempted',),
    'max_crushes': ('crushing_steps', 'boundary_unlayerings'),
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


def configs():
    """One explicit option map for both arms; caps are shared per whole call."""
    return dict(max_sectors=256, max_bases=10000, max_crushes=None,
        sector_order='diversified', sector_quantum=64, sector_method='transversal',
        max_pivots=10000, max_anchors=10000, lp_strategy='envelope',
        reduce_vertices=True, unlayer_boundary=True, max_tree_nodes=256,
        tree_model='source', max_hitting_subsets=10000,
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


def repeated_trefoils(k):
    from fastunknot.diagram import Diagram
    assert type(k) is int and k in (2, 4, 8, 16)
    word = [i for i in range(1, k+1) for _ in range(3)]
    diagram = Diagram.from_braid(k+1, word)
    return dict(id='T'+str(k), summands=k, braid=dict(strands=k+1, word=word),
                input_pd=[list(row) for row in diagram.pd])


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(canonical_bytes(value)).hexdigest()


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*') if p.is_file()
              and '__pycache__' not in p.parts and p.suffix != '.pyc']
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_bytes(value)+b'\n')
