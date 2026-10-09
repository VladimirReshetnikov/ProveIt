"""Independent stable-vertex and cache audit against fresh manifold roots."""
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from batched_descent_research.fixtures import source_fixture, inflate_disjoint
from fastunknot.cocycle_peeling import CocyclePeelingState
from fastunknot.normal_cocycle import local_coordinates
from fastunknot.normal_surface_geometry import _prepare


def audit(state):
    fresh = _prepare(state.triangulation, lambda: None)
    old_to_new, new_to_old, literal = {}, {}, {}
    boundary = {fresh['vertex_roots'][4*t+v] for t, f in fresh['boundary_faces']
                for v in range(4) if v != f}
    for t, row in enumerate(state.heights):
        coordinates = local_coordinates(row)
        for v in range(4):
            stable, current = state._vertices[t][v], fresh['vertex_roots'][4*t+v]
            assert old_to_new.setdefault(stable, current) == current
            assert new_to_old.setdefault(current, stable) == stable
            assert state.index.link_euler[stable] == (1 if current in boundary else 2)
            literal.setdefault(stable, []).append((coordinates[v], state._corners[t][v]))
    assert set(literal) == set(state.index.link_euler)
    for stable, records in literal.items():
        records.sort()
        assert state.index.minimum(stable) == records[0][0]
        assert state.index.count(stable) == len(records)
        assert state.index.prefix(stable) == tuple(records[:13])
    state.index.verify_invariants()
    return len(literal)


def main():
    rng = random.Random(991071)
    trials = []
    for family in ('layered', 'unknot', 'trefoil', 'figure_eight'):
        initial, h, source = source_fixture(family, 8)
        raw, h, _, _ = inflate_disjoint(initial, h, 8)
        state = CocyclePeelingState(raw, h)
        vertices, batches, moves = audit(state), 0, 0
        for step in range(12):
            candidates = state.score_candidates()['candidates']
            if not candidates:
                break
            rng.shuffle(candidates)
            chosen, removed = [], set()
            for candidate in candidates:
                support = {row['tetrahedron'] for row in candidate['region']}
                if support.isdisjoint(removed):
                    chosen.append(candidate)
                    removed.update(support)
                if len(chosen) == 1 + step % 4:
                    break
            prior = state.full_summary()
            expected = state.score_candidate_batch(chosen)
            sites = [dict(tetrahedron=c['tetrahedron'], vertices=c['vertices']) for c in chosen]
            result = state.apply_batch(sites)
            actual = state.full_summary()
            assert result['peeling'] == expected
            assert actual['peeled_euler'] - prior['peeled_euler'] == expected['peeled_euler_gain']
            assert prior['peeled_pieces'] - actual['peeled_pieces'] == expected['peeled_piece_saving']
            assert audit(state) == vertices
            batches += 1
            moves += len(chosen)
        trials.append(dict(family=family, vertices=vertices, batches=batches, moves=moves,
                           final_tetrahedra=len(state.triangulation['tetrahedra'])))
    report = dict(seed=991071, passed=True, cases=trials,
                  checks=['fresh/stable vertex bijection', 'boundary/interior link type',
                          'all triangle records', 'minimum and thirteen-prefix exactness',
                          'AVL invariants', 'collective score versus full cells'])
    path = Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
