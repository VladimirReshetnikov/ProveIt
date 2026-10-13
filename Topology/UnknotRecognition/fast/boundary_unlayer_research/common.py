"""Fresh pins and independent Regina source conversion for this audit."""
from hashlib import sha256
import json
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
COLLARS = ROOT/'fast/boundary_transversal_research/data/provenance/layer-refuter.json'
SEARCH_CONFIGS = {
    'dfs': dict(model='source', strategy='envelope', max_nodes=256,
                max_pivots=10000, max_anchors=10000,
                max_ellipsoid_iterations=10000, max_feasibility_calls=10000),
    'transversal_conflicts': dict(candidate_policy='conflicts', strategy='envelope',
                max_nodes=256, max_pivots=10000, max_anchors=10000,
                max_hitting_subsets=10000,
                max_ellipsoid_iterations=10000, max_feasibility_calls=10000),
}
CAP_STATS = dict(max_nodes='nodes_attempted', max_pivots='lp_pivots',
                max_anchors='anchors_tested', max_hitting_subsets='hitting_subsets_tested',
                max_ellipsoid_iterations='lp_ellipsoid_iterations',
                max_feasibility_calls='lp_feasibility_calls')
BENCHMARK_PROTOCOL = dict(warmups_per_arm=1, paired_rounds=3, aa_pairs=1,
                          discovery_limit_seconds=20,
                          supplied_method='dfs', diagram_method='transversal_conflicts',
                          source_ids=['layered_torus_1', 'layered_torus_4', 'layered_torus_8'],
                          diagram_ids=['circle', 'trefoil', 'figure_eight'])


def normalized_result(value):
    """Only diagnostic wall time is excluded from deterministic result pins."""
    if isinstance(value, dict):
        return {k: normalized_result(v) for k, v in value.items() if k != 'discovery_seconds'}
    if isinstance(value, (list, tuple)):
        return [normalized_result(v) for v in value]
    return value


def benchmark_bindings(audit):
    """Predeclared common-complete controls, bound to the full fresh audit."""
    result = []
    for name in BENCHMARK_PROTOCOL['source_ids']:
        record, = [r for r in audit['supplied_reductions'] if r['id'] == name and r['method'] == 'dfs']
        result.append(dict(kind='supplied', id=name, source=record['arms']['baseline']['source'], arms=record['arms']))
    for name in BENCHMARK_PROTOCOL['diagram_ids']:
        record, = [r for r in audit['diagrams'] if r['id'] == name]
        result.append(dict(kind='diagram', id=name, input_pd=record['input_pd'], arms=record['arms']))
    return result


def diagram_options(*, scan_only=False, peel=False):
    return dict(sector_method='transversal', tree_model='source',
                transversal_candidate_policy='conflicts', max_hitting_subsets=10000,
                max_tree_nodes=0 if scan_only else 256, max_pivots=10000,
                max_anchors=10000, max_ellipsoid_iterations=10000,
                max_feasibility_calls=10000, unlayer_boundary=peel)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*') if p.is_file() and p.suffix in ('.py', '.md', '.json')]
    paths += [COLLARS, ROOT/'fast/normal_orbit_research/fixtures.py']
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}


def regina_triangulation(source):
    import regina
    result = regina.Triangulation3()
    tetrahedra = result.newTetrahedra(len(source['tetrahedra']))
    for t, row in enumerate(source['tetrahedra']):
        for f, record in enumerate(row):
            if record is not None and tetrahedra[t].adjacentTetrahedron(f) is None:
                tetrahedra[t].join(f, tetrahedra[record['tetrahedron']],
                                   regina.Perm4(*record['permutation']))
    return result


def face_pairing(triangulation):
    return dict(tetrahedra=[[
        None if tet.adjacentTetrahedron(f) is None else
        dict(tetrahedron=tet.adjacentTetrahedron(f).index(),
             permutation=[tet.adjacentGluing(f)[j] for j in range(4)])
        for f in range(4)] for tet in triangulation.tetrahedra()])


def topology_summary(triangulation, *, solid_torus=False):
    assert triangulation.isValid() and triangulation.isOrientable()
    assert triangulation.countComponents() == triangulation.countBoundaryComponents() == 1
    assert triangulation.countVertices() == 1
    assert triangulation.boundaryComponent(0).eulerChar() == 0
    result = dict(valid=True, orientable=True, vertices=1, boundary_components=1,
                  boundary_euler=0, homology=str(triangulation.homology()))
    if solid_torus:
        assert triangulation.isSolidTorus()
        result['solid_torus'] = True
    return result
