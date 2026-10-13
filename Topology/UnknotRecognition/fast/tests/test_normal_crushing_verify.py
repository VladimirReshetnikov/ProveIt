"""Crushing replay, erased cycles, finite boundary census and hostile packets."""

from copy import deepcopy
import importlib.util
from itertools import permutations
from random import Random
import unittest
from unittest.mock import patch

from fastunknot.normal_crushing_verify import quotient_census, verify_normal_crushing
from normal_orbit_research.fixtures import layered_torus, boundary_cap
from tests.test_normal_surface_orbits import relabel


def triangulation(specifications):
    return {'tetrahedra': [[None if entry is None else dict(tetrahedron=entry[0],
                            permutation=list(entry[1])) for entry in faces]
                          for faces in specifications]}


def union(*triangulations):
    output = []
    for tri in triangulations:
        offset = len(output)
        output.extend([[None if r is None else dict(tetrahedron=offset+r['tetrahedron'],
                       permutation=list(r['permutation'])) for r in row]
                       for row in tri['tetrahedra']])
    return {'tetrahedra': output}


def packet(rows, retained=(), quotient=None, components=(), selected=None):
    quotient = {'tetrahedra': []} if quotient is None else deepcopy(quotient)
    return dict(schema='normal-ray-crushing-v1', coordinates=deepcopy(rows),
                retained_tetrahedra=list(retained), triangulation=quotient,
                components=deepcopy(list(components)), torus_component=selected,
                successor=deepcopy(quotient) if selected is not None else None)


def rejected_disc():
    # First retained counterexample in filtered-atlas-native.json, two_tet_1.
    source, _ = layered_torus(1)
    source = deepcopy(source)
    source['tetrahedra'][0][2] = dict(tetrahedron=1, permutation=[0, 1, 2, 3])
    source['tetrahedra'].append([None, None, dict(tetrahedron=0,
                                               permutation=[0, 1, 2, 3]), None])
    return source, [[1, 1, 1, 1, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0]]


def isolated_cycle():
    # Frozen independent Regina 7.4 oracle: a connected primitive extreme
    # sphere with an erased six-face quad cycle, and its numbered quotient.
    source = triangulation([
        [None, None, (2, (0,1,2,3)), None],
        [(4,(3,1,2,0)), (3,(0,3,2,1)), (2,(0,1,3,2)), None],
        [(5,(2,1,0,3)), (3,(0,2,1,3)), (0,(0,1,2,3)), (1,(0,1,3,2))],
        [(6,(1,0,2,3)), (7,(3,0,1,2)), (2,(0,2,1,3)), (1,(0,3,2,1))],
        [(7,(3,1,2,0)), (6,(0,3,2,1)), (5,(0,1,3,2)), (1,(3,1,2,0))],
        [(7,(2,1,0,3)), (6,(0,2,1,3)), (2,(2,1,0,3)), (4,(0,1,3,2))],
        [(7,(1,0,2,3)), (3,(1,0,2,3)), (5,(0,2,1,3)), (4,(0,3,2,1))],
        [(3,(1,2,3,0)), (6,(1,0,2,3)), (5,(2,1,0,3)), (4,(3,1,2,0))],
    ])
    rows = [[0]*7, [0,0,0,1,0,0,0], [0,0,1,0,0,0,0], [0,1,0,0,0,0,0],
            [0,0,0,0,0,0,1], [0,0,0,0,0,1,0], [0,0,0,0,1,0,0], [1,0,0,0,0,0,0]]
    quotient = triangulation([
        [None, None, (2,(0,1,2,3)), None],
        [(4,(3,1,2,0)), (3,(0,3,2,1)), (2,(0,1,3,2)), None],
        [(4,(2,1,0,3)), (3,(0,2,1,3)), (0,(0,1,2,3)), (1,(0,1,3,2))],
        [(4,(1,0,2,3)), (4,(3,0,1,2)), (2,(0,2,1,3)), (1,(0,3,2,1))],
        [(3,(1,2,3,0)), (3,(1,0,2,3)), (2,(2,1,0,3)), (1,(3,1,2,0))],
    ])
    return source, packet(rows, (0,1,2,3,7), quotient,
                         [dict(tetrahedra=list(range(5)), boundary_euler=[0])], 0)


class NormalCrushingVerifierTests(unittest.TestCase):
    def test_positive_support_rank_uses_exact_rationals(self):
        # Frozen Regina vertex 28 on the stage-0 eight-tetrahedron fixture.
        # Its support has 15 columns and exact rank 14; floating elimination
        # incorrectly gives rank 15 despite the small integer input entries.
        from fastunknot.normal_crushing import crush_normal_ray
        source = triangulation([
            [(3,(3,1,2,0)), (2,(0,3,2,1)), (1,(0,1,3,2)), None],
            [(3,(2,1,0,3)), (2,(0,2,1,3)), (5,(0,1,2,3)), (0,(0,1,3,2))],
            [(3,(1,0,2,3)), (3,(3,0,1,2)), (1,(0,2,1,3)), (0,(0,3,2,1))],
            [(2,(1,2,3,0)), (2,(1,0,2,3)), (1,(2,1,0,3)), (0,(3,1,2,0))],
            [(7,(3,1,2,0)), (6,(0,3,2,1)), (5,(0,1,3,2)), None],
            [(7,(2,1,0,3)), (6,(0,2,1,3)), (1,(0,1,2,3)), (4,(0,1,3,2))],
            [(7,(1,0,2,3)), None, (5,(0,2,1,3)), (4,(0,3,2,1))],
            [None, (6,(1,0,2,3)), (5,(2,1,0,3)), (4,(3,1,2,0))],
        ])
        rows = [[1,1,0,0,0,0,1], [1,2,0,0,0,0,0], [1,0,1,0,0,0,0],
                [0,1,0,0,0,0,1], [0,3,0,0,0,0,0], [0,2,0,0,0,1,0],
                [0,0,0,1,0,0,0], [0,2,0,0,0,1,0]]
        result = crush_normal_ray(source, rows)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(verify_normal_crushing(source, result['certificate']))

    def test_empty_ball_closed_and_disconnected_boundary_census(self):
        torus, _ = layered_torus(2)
        ball = {'tetrahedra': [[None]*4]}
        sphere = {'tetrahedra': [[dict(tetrahedron=1-t, permutation=list(range(4)))
                                 for _ in range(4)] for t in range(2)]}
        self.assertEqual(quotient_census({'tetrahedra': []}), [])
        self.assertEqual(quotient_census(ball), [dict(tetrahedra=[0], boundary_euler=[2])])
        self.assertEqual(quotient_census(sphere), [dict(tetrahedra=[0,1], boundary_euler=[])])
        self.assertEqual(quotient_census(union(ball, torus, sphere, ball)), [
            dict(tetrahedra=[0], boundary_euler=[2]),
            dict(tetrahedra=[1,2], boundary_euler=[0]),
            dict(tetrahedra=[3,4], boundary_euler=[]),
            dict(tetrahedra=[5], boundary_euler=[2]),
        ])

    def test_meridian_empty_and_ball_quotients_including_one_tetrahedron(self):
        for n in (1,2,4,7):
            tri, rows = layered_torus(n)
            self.assertTrue(verify_normal_crushing(tri, packet(rows)))
            self.assertTrue(verify_normal_crushing(tri, packet([[hex(v) for v in row] for row in rows])))
            capped, extension = boundary_cap(tri, rows)
            ball = {'tetrahedra': [[None]*4]}
            proof = packet(extension, (n,), ball, [dict(tetrahedra=[0], boundary_euler=[2])])
            self.assertTrue(verify_normal_crushing(capped, proof))

    def test_rejected_disc_preserves_a_smaller_torus_and_relabelled_permutations(self):
        tri, rows = rejected_disc()
        torus, _ = layered_torus(1)
        proof = packet(rows, (0,), torus, [dict(tetrahedra=[0], boundary_euler=[0])], 0)
        self.assertTrue(verify_normal_crushing(tri, proof))
        rng = Random(11920261012)
        for _ in range(24):
            changed, vector = relabel(tri, rows, rng)
            retained = next(t for t,row in enumerate(vector) if not any(row[4:]))
            faces = [None if r is None or r['tetrahedron'] != retained else
                     dict(tetrahedron=0, permutation=list(r['permutation']))
                     for r in changed['tetrahedra'][retained]]
            expected = {'tetrahedra': [faces]}
            result = packet(vector, (retained,), expected,
                            [dict(tetrahedra=[0], boundary_euler=[0])], 0)
            self.assertTrue(verify_normal_crushing(changed, result))

    def test_erased_six_face_cycle_does_not_prevent_sphere_crushing(self):
        tri, proof = isolated_cycle()
        self.assertTrue(verify_normal_crushing(tri, proof))
        self.assertEqual(quotient_census(proof['triangulation']), proof['components'])

    def test_saved_quotient_replays_with_all_producer_geometry_disabled(self):
        from fastunknot import normal_crushing as producer
        tri, proof = isolated_cycle()
        with patch.object(producer, 'crush_normal_ray', side_effect=AssertionError('producer used')), \
                patch.object(producer, '_trace_quotient', side_effect=AssertionError('tracer used')), \
                patch.object(producer, '_component', side_effect=AssertionError('extractor used')), \
                patch.object(producer, 'quotient_census', side_effect=AssertionError('producer census used')):
            self.assertTrue(verify_normal_crushing(tri, proof))

    def test_full_source_extremality_primitivity_and_positive_nonvertex_hypotheses(self):
        tri, rows = layered_torus(1)
        for bad in ([[2*v for v in rows[0]]], [[(1 << 600)*v for v in rows[0]]],
                    [[2,2,1,1,0,0,1]],  # Primitive disconnected meridian + vertex disc.
                    [[1,1,1,1,0,0,0]],  # A vertex link gives no strict decrease.
                    [[0,0,0,0,0,1,0]],  # Mobius band has chi zero.
                    [[0]*7], [[1,1,0,0,1,0,1]]):
            self.assertFalse(verify_normal_crushing(tri, packet(bad)), bad)
        for bad in ([[True,1,0,0,0,0,1]], [['1',1,0,0,0,0,1]],
                    [[1.0,1,0,0,0,0,1]], [['0xg',1,0,0,0,0,1]]):
            self.assertFalse(verify_normal_crushing(tri, packet(bad)))

    def test_hostile_packet_schema_source_indices_census_and_successor(self):
        tri, rows = rejected_disc()
        torus, _ = layered_torus(1)
        original = packet(rows, (0,), torus, [dict(tetrahedra=[0], boundary_euler=[0])], 0)
        mutants = []
        for field, value in (('schema','bad'), ('coordinates',[]), ('retained_tetrahedra',[False]),
                             ('retained_tetrahedra',[1]), ('retained_tetrahedra',[0,1]),
                             ('components',[]), ('torus_component',True), ('torus_component',None),
                             ('successor',None), ('triangulation', {'tetrahedra':[]})):
            bad = deepcopy(original); bad[field] = value; mutants.append(bad)
        bad = deepcopy(original); bad['extra'] = 1; mutants.append(bad)
        bad = deepcopy(original); del bad['successor']; mutants.append(bad)
        bad = deepcopy(original); bad['components'][0]['boundary_euler'] = [False]; mutants.append(bad)
        bad = deepcopy(original); bad['components'][0]['tetrahedra'] = [0,0]; mutants.append(bad)
        bad = deepcopy(original); bad['triangulation']['tetrahedra'][0][0]['tetrahedron'] = False; mutants.append(bad)
        bad = deepcopy(original); bad['successor']['tetrahedra'][0][0]['permutation'] = [1,3,2,0]; mutants.append(bad)
        for bad in mutants:
            self.assertFalse(verify_normal_crushing(tri, bad), bad)
        source_bad = deepcopy(tri); source_bad['tetrahedra'][0][0] = None
        self.assertFalse(verify_normal_crushing(source_bad, original))

    def test_every_component_gets_manifold_and_orientability_validation(self):
        torus, _ = layered_torus(1)
        ideal = triangulation([
            [(1,(1,3,0,2)), (1,(2,0,3,1)), (1,(0,3,2,1)), (1,(2,1,0,3))],
            [(0,(1,3,0,2)), (0,(2,0,3,1)), (0,(0,3,2,1)), (0,(2,1,0,3))],
        ])
        with self.assertRaisesRegex(ValueError, 'vertex link'):
            quotient_census(union(torus, ideal))
        nonorientable = triangulation([[(0,(1,2,0,3)), (0,(2,0,1,3)), None, None]])
        with self.assertRaisesRegex(ValueError, 'not orientable'):
            quotient_census(union(torus, nonorientable))
        bad = deepcopy(torus); bad['tetrahedra'][0][1] = None
        with self.assertRaisesRegex(ValueError, 'reciprocal'):
            quotient_census(union(torus, bad))
        for bad in ({}, {'tetrahedra':None}, {'tetrahedra':[(None,)*4]},
                    {'tetrahedra':[[dict(tetrahedron=True, permutation=[0,1,2,3])]+[None]*3]}):
            with self.assertRaises((ValueError,TypeError)):
                quotient_census(bad)

    def test_callback_exceptions_propagate_through_all_replay_stages(self):
        tri, proof = isolated_cycle()
        calls = 0
        def count():
            nonlocal calls
            calls += 1
        self.assertTrue(verify_normal_crushing(tri, proof, check=count))
        total = calls
        class Cancel:
            def __init__(self, limit, error):
                self.calls, self.limit, self.error = 0, limit, error
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.limit:
                    raise self.error
        for error in (ValueError('external'), TypeError('external'), RuntimeError('external')):
            for limit in (1, total//2, total):
                with self.assertRaises(type(error)) as caught:
                    verify_normal_crushing(tri, proof, check=Cancel(limit,error))
                self.assertIs(caught.exception, error)
            with self.assertRaises(type(error)) as caught:
                quotient_census({'tetrahedra':[]}, check=Cancel(1,error))
            self.assertIs(caught.exception, error)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_random_pairing_census_against_independent_manifold_oracle(self):
        from normal_orbit_research.fixtures import regina_triangulation
        rng = Random(119761)
        perms = list(permutations(range(4)))
        accepted = 0
        for i in range(160):
            n = 1+i % 4
            faces = [[None]*4 for _ in range(n)]
            nodes = list(range(4*n)); rng.shuffle(nodes)
            for a,b in zip(nodes[::2],nodes[1::2]):
                if rng.random() < .25:
                    continue
                t,f = divmod(a,4); u,g = divmod(b,4)
                p = rng.choice([p for p in perms if p[f] == g])
                faces[t][f] = dict(tetrahedron=u,permutation=list(p))
                faces[u][g] = dict(tetrahedron=t,permutation=[p.index(v) for v in range(4)])
            raw = {'tetrahedra':faces}
            native = regina_triangulation(raw)
            expected = native.isValid() and native.isOrientable() and not native.isIdeal()
            try:
                census = quotient_census(raw)
            except ValueError:
                self.assertFalse(expected, raw)
            else:
                self.assertTrue(expected, raw)
                observed = sorted((len(c['tetrahedra']),c['boundary_euler']) for c in census)
                oracle = sorted((c.size(),sorted(int(b.eulerChar()) for b in c.boundaryComponents()))
                                for c in native.triangulateComponents())
                self.assertEqual(observed,oracle)
                accepted += 1
        self.assertEqual(accepted,26)


if __name__ == '__main__':
    unittest.main()
