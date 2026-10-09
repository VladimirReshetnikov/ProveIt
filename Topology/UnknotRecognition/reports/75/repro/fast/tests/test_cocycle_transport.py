from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.cocycle_transport import (
    bipyramid_cocycle_score, cocycle_collapse_candidates, descend_cocycle,
    transport_cocycle,
)
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from normal_orbit_research.fixtures import layered_torus


def cell_score(five):
    c, d, e, a, b = five
    span = lambda *x: max(x)-min(x)
    pieces = (span(a,b,c,d)+span(a,b,d,e)+span(a,b,e,c)
              -span(a,c,d,e)-span(b,c,d,e))
    arcs = span(a,b,c)+span(a,b,d)+span(a,b,e)-span(c,d,e)
    return abs(a-b)-arcs+pieces, pieces


class CocycleTransportTests(unittest.TestCase):
    def test_all_small_height_orders_and_binary_scaling(self):
        for heights in product(range(-2, 3), repeat=5):
            score = bipyramid_cocycle_score(heights)
            euler, pieces = cell_score(heights)
            self.assertEqual(euler, -score['euler_loss'])
            self.assertEqual(pieces, score['normal_disc_increase'])
            self.assertGreaterEqual(score['gap'], 0)
            self.assertGreaterEqual(pieces, score['gap'])
        source = [0, -1, 1, 3, 4]
        score = bipyramid_cocycle_score(source)
        scale, offset = 1 << 20000, -(1 << 20007)
        self.assertEqual(bipyramid_cocycle_score([scale*x+offset for x in source]),
                         {k: scale*v for k, v in score.items()})
        self.assertEqual(bipyramid_cocycle_score([-x for x in source]), score)

    def test_round_trip_and_independent_checker(self):
        for n in (2, 4, 12):
            before, _ = layered_torus(n)
            initial = rank_one_cocycle_seed(before)
            up = pachner_23(before, 0, 0)
            forward = transport_cocycle(before, initial['heights'], up['triangulation'], up['certificate'])
            with patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
                 patch('fastunknot.normal_cocycle.local_coordinates', side_effect=AssertionError), \
                 patch('fastunknot.normal_cocycle.rank_one_cocycle_seed', side_effect=AssertionError):
                self.assertTrue(verify_cocycle_transport(before, initial['heights'],
                    up['triangulation'], forward['certificate']))
            down = pachner_32(up['triangulation'], n-2, [0, 1])
            reverse = transport_cocycle(up['triangulation'], forward['heights'],
                                       down['triangulation'], down['certificate'])
            self.assertEqual(forward['certificate']['euler_jump'],
                             -reverse['certificate']['euler_jump'])
            self.assertEqual(forward['certificate']['normal_disc_jump'],
                             -reverse['certificate']['normal_disc_jump'])
            reseed = rank_one_cocycle_seed(down['triangulation'])
            self.assertEqual(reverse['coordinates'], reseed['coordinates'])

    def test_mutated_evidence_and_global_cochain_rejection(self):
        before, _ = layered_torus(4)
        seed = rank_one_cocycle_seed(before)
        result = pachner_23(before, 0, 0)
        after = result['triangulation']
        proof = transport_cocycle(before, seed['heights'], after, result['certificate'])['certificate']
        for bad in (None, {}, dict(proof, extra=1), dict(proof, schema='wrong'),
                    dict(proof, heights=[]), dict(proof, coordinates=[]),
                    dict(proof, euler_jump=True), dict(proof, normal_disc_jump=False)):
            self.assertFalse(verify_cocycle_transport(before, seed['heights'], after, bad))
        for field in ('euler_jump', 'normal_disc_jump'):
            bad = deepcopy(proof)
            bad[field] += 1
            self.assertFalse(verify_cocycle_transport(before, seed['heights'], after, bad))
        for field, i, j in (('coordinates', 0, 0), ('heights', 0, 1)):
            bad = deepcopy(proof)
            bad[field][i][j] += 1
            self.assertFalse(verify_cocycle_transport(before, seed['heights'], after, bad))
        for i in range(5):
            bad = deepcopy(proof)
            bad['bipyramid_heights'][i] += 1
            self.assertFalse(verify_cocycle_transport(before, seed['heights'], after, bad))
        invalid = deepcopy(seed['heights'])
        invalid[0][1] += 1
        self.assertFalse(verify_cocycle_transport(before, invalid, after, proof))
        with self.assertRaises(NormalOrbitError):
            transport_cocycle(before, invalid, after, result['certificate'])
        shifted = [[x+13*(t+1) for x in row] for t, row in enumerate(seed['heights'])]
        self.assertTrue(verify_cocycle_transport(before, shifted, after, proof))

    def test_binary_coordinates_limits_cancellation_and_immutability(self):
        raw, _ = layered_torus(4)
        seed = rank_one_cocycle_seed(raw)
        up = pachner_23(raw, 0, 0)
        after, move = up['triangulation'], up['certificate']
        saved = deepcopy((raw, seed, after, move))
        ordinary = transport_cocycle(raw, seed['heights'], after, move)
        scaled = [[(1 << 20000)*x for x in row] for row in seed['heights']]
        large = transport_cocycle(raw, scaled, after, move)
        self.assertEqual(ordinary['stats']['work'], large['stats']['work'])
        self.assertEqual(large['coordinates'], [[(1 << 20000)*x for x in row]
                                             for row in ordinary['coordinates']])
        exact = ordinary['stats']['work']
        self.assertEqual(transport_cocycle(raw, seed['heights'], after, move, max_work=exact), ordinary)
        with self.assertRaises(CocycleLimit):
            transport_cocycle(raw, seed['heights'], after, move, max_work=exact-1)
        for operation in (lambda cb: transport_cocycle(raw, seed['heights'], after, move, check=cb),
                          lambda cb: verify_cocycle_transport(raw, seed['heights'], after,
                                                             ordinary['certificate'], check=cb)):
            count = [0]
            def tick():
                count[0] += 1
            operation(tick)
            for stop in (1, count[0]//2, count[0]):
                count[0] = 0
                def cancel():
                    tick()
                    if count[0] == stop:
                        raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                    operation(cancel)
        self.assertEqual((raw, seed, after, move), saved)

    def test_every_scored_site_has_its_claimed_global_jump(self):
        rng = random.Random(202610091)
        raw, _ = layered_torus(6)
        h = rank_one_cocycle_seed(raw)['heights']
        for _ in range(12):
            sites = [(t, f) for t, row in enumerate(raw['tetrahedra']) for f, r in enumerate(row)
                     if r is not None and r['tetrahedron'] != t]
            t, f = rng.choice(sites)
            up = pachner_23(raw, t, f)
            result = transport_cocycle(raw, h, up['triangulation'], up['certificate'])
            raw, h = up['triangulation'], result['heights']
        initial = _coordinates(_prepare(raw, lambda: None), result['coordinates'], lambda: None)
        candidates = cocycle_collapse_candidates(raw, h)['candidates']
        self.assertGreater(len(candidates), 1)
        for candidate in candidates:
            down = pachner_32(raw, candidate['tetrahedron'], candidate['vertices'])
            result = transport_cocycle(raw, h, down['triangulation'], down['certificate'])
            final = _coordinates(_prepare(down['triangulation'], lambda: None),
                                 result['coordinates'], lambda: None)
            self.assertEqual(final['euler_characteristic']-initial['euler_characteristic'],
                             candidate['euler_gain'])
            self.assertEqual(initial['normal_disks']-final['normal_disks'],
                             candidate['normal_disc_saving'])

    def test_obstruction_descent_has_verified_compressing_disk(self):
        path = Path(__file__).resolve().parents[2]/'synthesis/data/coherent-obstruction-certificate.json'
        if not path.exists():
            self.skipTest('repository obstruction fixture is not present')
        raw = json.loads(path.read_text())['moves'][-1]['triangulation']
        h = rank_one_cocycle_seed(raw)['heights']
        result = descend_cocycle(raw, h)
        self.assertEqual(result['stats']['euler_gain'], 4)
        self.assertEqual(result['stats']['moves'], 6)
        self.assertEqual(sum(map(sum, result['coordinates'])), 8)
        current, heights = raw, h
        for step in result['moves']:
            self.assertTrue(verify_cocycle_transport(current, heights, step['triangulation'], step['transport']))
            current, heights = step['triangulation'], step['transport']['heights']
        disk = normal_compressing_disk_count(current, result['coordinates'], record_certificate=True)
        self.assertEqual(disk['compressing_disk_components'], 1)
        self.assertTrue(verify_normal_disk_count_certificate(current, result['coordinates'], disk['certificate']))
        self.assertEqual(descend_cocycle(raw, h, max_moves=0)['status'], 'MOVE_LIMIT')


if __name__ == '__main__':
    unittest.main()
