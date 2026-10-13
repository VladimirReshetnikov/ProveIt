"""Solver-free replay of the finite two-trefoil conflict lower bound."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.interlace import visible_factors_interlacement, verify_interlacement_certificate
from fastunknot.normal_crushing_chain import verify_crushing_chain
from .common import digest, load, source_hashes, verify_provenance
from .standard import observation

CORE = (5, 6, 7, 11, 17, 19, 20)
HITTING_SET = (3, 5, 7, 11, 14)


def verify_factors(state, fixtures):
    item = next(r for r in fixtures['records'] if r['id'] == 'tt')
    diagram = Diagram.from_pd(state['input_pd'])
    assert item['pd'] == state['input_pd']
    assert item['pd_sha256'] == digest(diagram.pd)
    assert item['braid'] == dict(strands=3, word=[1, 1, 1, 2, 2, 2])
    assert diagram.pd == Diagram.from_braid(3, item['braid']['word']).pd
    factors, certificate = visible_factors_interlacement(diagram)
    assert certificate == item['factor_certificate']
    assert verify_interlacement_certificate([d//4 for d in diagram.traversal()], certificate)
    assert len(factors) == len(item['factors']) == 2
    for factor, saved in zip(factors, item['factors']):
        assert saved['base'] == 'T'
        base = Diagram.from_braid(2, [1, 1, 1])
        mapping = saved['base_edge_to_factor_edge']
        assert sorted(mapping) == list(range(6))
        assert tuple(tuple(mapping[v] for v in row) for row in base.pd) == factor.pd
        assert [list(row) for row in factor.pd] == saved['factor_pd']
        assert [list(row) for row in base.pd] == saved['base_pd']
        assert digest(factor.pd) == saved['factor_pd_sha256']
        assert saved['crossing_permutation'] == list(range(3))
        assert saved['slot_rotations'] == [0]*3 and saved['reflection_used'] is False
    return diagram, dict(braid=item['braid'], pd_sha256=digest(diagram.pd),
        crossing_components=certificate['crossing_components'],
        factor_ids=['T', 'T'], slot_preserving_maps=[r['base_edge_to_factor_edge'] for r in item['factors']])


def check_hypergraph(edges, *, check=lambda: None):
    """Prove tau(retained)=5 independently of the discovery heuristic."""
    assert len(edges) == 35 and all(edge and set(edge) <= set(range(23)) for edge in edges)
    edges = [set(edge) for edge in edges]
    assert all(set(HITTING_SET) & edge for edge in edges)
    # A short combinatorial core, independently checked against exact ray data.
    expected = [{3, 4}, {5}, {7, 12, 17, 21}, {10, 11, 14},
                {12, 14}, {7, 14, 18, 19}, {11, 16, 19}]
    assert [edges[i] for i in CORE] == expected
    first, second, A, B, C, D, E = expected
    assert first.isdisjoint(second)
    assert (first | second).isdisjoint(A | B | C | D | E)
    assert C == {12, 14} and not B & D & E and not A & E
    assert 12 not in B | D | E and 14 not in A | E
    # Also exhaust every four-subset of the complete 23-tetrahedron universe.
    # Monotonicity then excludes every smaller subset too.
    counts = [0]*len(edges)
    coverage = sha256()
    excluded = 0
    for candidate in combinations(range(23), 4):
        check()
        missing = next(i for i, edge in enumerate(edges) if set(candidate).isdisjoint(edge))
        counts[missing] += 1
        coverage.update((str(candidate)+':'+str(missing)+'\n').encode())
        assert any(set(candidate).isdisjoint(edges[i]) for i in CORE)
        excluded += 1
    assert excluded == comb(23, 4) == 8855
    packing_ids = (5, 17, 20, 13)
    assert all(edges[i].isdisjoint(edges[j]) for i, j in combinations(packing_ids, 2))
    return dict(retained_hypergraph_transversal_number=5, source_h_lower_bound=5,
        hitting_set=list(HITTING_SET), lower_bound_core_indices=list(CORE),
        four_subsets_excluded=excluded, first_disjoint_witness_counts=counts,
        coverage_sha256=coverage.hexdigest(), disjoint_packing_indices=list(packing_ids),
        disjoint_packing_size=4, source_h_upper_bound=None)


def audit(*, check=lambda: None):
    before = source_hashes()
    provenance = verify_provenance()
    state = load('generation/tt-state.json.gz')
    control = load('generation/tt-unlayer-control.json.gz')
    diagram, factors = verify_factors(state, load('generation/fixtures.json.gz'))
    assert state['status'] == 'PREPARED' and 'certificate' not in state
    assert state['native_pins_unchanged'] is True and control['native_pins_unchanged'] is True
    assert control['old_state_sha256'] == digest(state)
    v1, v2 = state['chain'], control['result']['partial_chain']
    assert v1['schema'] == 'diagram-crushing-v1' and v2['schema'] == 'diagram-crushing-v2'
    assert verify_crushing_chain(diagram, v1, check=check)
    assert verify_crushing_chain(diagram, v2, check=check)
    assert {k: v for k, v in v1.items() if k != 'schema'} == {k: v for k, v in v2.items() if k != 'schema'}
    source = v1['triangulation']
    key = digest(source)
    assert key == state['source_sha256'] == control['source_sha256']
    assert source == state['stage_sources'][key] and len(source['tetrahedra']) == 23
    assert len(v1['steps']) == 24
    assert len(v1['source_triangulation']['tetrahedra']) == 120
    assert len(v1['shelling']['triangulation']['tetrahedra']) == 114
    assert control['config'] == dict(unlayer_boundary=True, sector_method='transversal',
        transversal_candidate_policy='conflicts', max_tree_nodes=0, max_pivots=0, max_anchors=0)
    stats = control['result']['stats']
    assert control['result']['status'] == 'INCONCLUSIVE'
    assert stats['boundary_unlayerings'] == stats['boundary_unlayer_candidates'] == 0
    assert stats['boundary_unlayer_calls'] == 1
    assert stats['nodes_attempted'] == stats['lp_calls'] == stats['lp_pivots'] == 0
    assert stats['vertex_reduction_crushes'] == 24
    rays = state['raw_rays'][key]
    assert len(rays) == len({digest(r['coordinates']) for r in rays}) == 35
    witnesses = []
    for index, ray in enumerate(rays):
        check()
        obs, ranks = observation(source, ray['coordinates'], check=check)
        assert obs['canonical_euler'] == ray['euler_characteristic'] > 0
        assert obs['conflicts'] == ray['conflicts'] and obs['conflicts']
        assert obs['boundary_faces'] == [[17, 0], [20, 0]]
        assert ranks['triangle_columns'] == 92 and ranks['triangle_rank'] == 91
        witnesses.append(dict(index=index, coordinates_sha256=digest(ray['coordinates']),
                             observation=obs, rank_proof=ranks))
    graph = check_hypergraph([w['observation']['conflicts'] for w in witnesses], check=check)
    candidates = []
    for attempt in state['attempts']:
        if attempt.get('kind') != 'explicit_candidate':
            continue
        name = Path(attempt['candidate_file']).name
        saved = load('generation/'+name+'.gz')
        assert saved['source_sha256'] == key and saved['status'] == 'REFUTED'
        assert saved['B'] == attempt['B']
        refuter = saved['refuter']
        found = next(i for i, r in enumerate(rays) if r['coordinates'] == refuter['coordinates'])
        assert set(saved['B']).isdisjoint(witnesses[found]['observation']['conflicts'])
        candidates.append(dict(B=saved['B'], witness_index=found,
                              conflict=witnesses[found]['observation']['conflicts'],
                              status='REFUTED', retained_file=name+'.gz'))
    assert len(candidates) == 5
    assert source_hashes() == before, 'sources changed during replay'
    return dict(schema='conflict-composition-audit-v1', passed=True, source_sha256=before,
        generation_provenance_sha256=digest(provenance), fixture_source_sha256=key,
        regina_used=False, lp_used=False, q_cycle_elimination_used=False,
        diagram_factors=factors, initial_tetrahedra=120, shelled_tetrahedra=114,
        crushing_steps=24, tetrahedra=23, vertices=1, boundary_faces=[[17, 0], [20, 0]],
        v1_chain_verified=True, v2_chain_verified=True, same_labelled_endpoint=True,
        same_crushing_steps=True, optional_unlayerings=0,
        witnesses=witnesses, hypergraph=graph, candidate_refutations=candidates,
        negative_cone_verified=False, complete_recognition_verdict=None,
        scope='Finite positive root-ray lower bound on one authenticated supplied source; no full-cone upper bound, negative-cone certificate, asymptotic family, or quasi-polynomial claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check-evidence', type=Path)
    args = parser.parse_args()
    result = audit()
    if args.check_evidence:
        assert result == json.loads(args.check_evidence.read_text())
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(passed=result['passed'], witnesses=len(result['witnesses']),
        tetrahedra=result['tetrahedra'], hypergraph=result['hypergraph'],
        negative_cone_verified=False, optional_unlayerings=0, source_files=len(result['source_sha256'])), indent=2))


if __name__ == '__main__':
    main()
