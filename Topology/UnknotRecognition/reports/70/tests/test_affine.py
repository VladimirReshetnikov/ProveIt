from collections import Counter
import copy
import json
import random
import unittest
from affine_orbits import BulkIndex, SparseOverlay, Model, Edge, Weight, Defect, wire
from affine_orbits.core import integer, digest
from affine_orbits.guard import split_edge, from_pairing_groups, UnsupportedModel
from affine_orbits.certificate import make_certificate
from affine_orbits.checker import verify
from oracle import expanded


def random_model(rng, W=None):
    W = W or rng.randrange(1, 25)
    v = rng.randrange(1, 7)
    D = rng.randrange(1, 5)
    e = tuple(Edge(rng.randrange(v), rng.randrange(v), rng.choice((-1, 1)), rng.randrange(W))
              for _ in range(rng.randrange(12)))
    weights = []
    for _ in range(rng.randrange(14)):
        a = rng.randrange(W)
        b = rng.randrange(a + 1, W + 1)
        weights.append(Weight(rng.randrange(v), a, b,
                              tuple(rng.randrange(-3, 4) for _ in range(D))))
    return Model(v, W, D, e, tuple(weights))


def random_defect(rng, m):
    return Defect(rng.randrange(m.vertices), rng.randrange(m.sheets),
                  rng.randrange(m.vertices), rng.randrange(m.sheets),
                  tuple(rng.randrange(-2, 3) for _ in range(m.dimension)))


class Correctness(unittest.TestCase):
    def assert_oracle(self, index, overlay=None, all_pairs=False):
        if overlay is None:
            overlay = SparseOverlay(index)
        m = index.snapshot()
        hist, labels, values = expanded(m, overlay.defects)
        self.assertEqual(hist, overlay.histogram)
        self.assertEqual(len(values), overlay.component_count)
        for u in range(m.vertices):
            for x in range(m.sheets):
                self.assertEqual(values[labels[u * m.sheets + x]], overlay.weight(u, x))
        for val in hist:
            witness = overlay.representative(val)
            self.assertIsNotNone(witness)
            u, x = witness
            self.assertEqual(values[labels[u * m.sheets + x]], val)
        if all_pairs:
            for x in range(m.vertices * m.sheets):
                for y in range(m.vertices * m.sheets):
                    u, a = divmod(x, m.sheets)
                    v, b = divmod(y, m.sheets)
                    self.assertEqual(labels[x] == labels[y], overlay.same_component(u, a, v, b))

    def test_exhaustive_two_generators(self):
        count = 0
        for W in range(1, 9):
            maps = [(s, a) for s in (-1, 1) for a in range(W)]
            for s, a in maps:
                for t, b in maps:
                    weights = (Weight(0, 0, W, (1, -2)),
                               Weight(0, 0, (W + 1) // 2, (2, 3)))
                    m = Model(1, W, 2, (Edge(0, 0, s, a), Edge(0, 0, t, b)), weights)
                    index = BulkIndex(m)
                    self.assert_oracle(index, all_pairs=True)
                    self.assertTrue(verify(m, [], make_certificate(index)))
                    count += 1
        self.assertEqual(count, 816)

    def test_random_graphs_and_defects(self):
        rng = random.Random(261009501)
        for trial in range(800):
            m = random_model(rng)
            index = BulkIndex(m)
            self.assert_oracle(index)
            overlay = SparseOverlay(index)
            for _ in range(rng.randrange(13)):
                overlay.add(random_defect(rng, m))
            self.assert_oracle(index, overlay)
            self.assertLessEqual(len(overlay.histogram), 2 * len(m.weights) + 3 * len(index.components) + len(overlay.defects))
            if trial % 10 == 0:
                self.assertTrue(verify(m, overlay.defects, make_certificate(index, overlay)))

    def test_random_epoch_updates(self):
        rng = random.Random(261009502)
        for _ in range(60):
            m = random_model(rng, W=rng.randrange(1, 65))
            index = BulkIndex(m)
            overlay = SparseOverlay(index)
            for _ in range(8):
                overlay.add(random_defect(rng, m))
            for _ in range(30):
                root = rng.choice(list(index.components))
                changed = index.add_root_map(root, rng.choice((-1, 1)), rng.randrange(m.sheets))
                if changed:
                    with self.assertRaises(RuntimeError):
                        _ = overlay.histogram
                    overlay.rebase()
                self.assert_oracle(index, overlay)
                fresh = BulkIndex(index.snapshot())
                self.assertEqual(index.histogram, fresh.histogram)
            for comp in index.components.values():
                self.assertLessEqual(comp.rebuilds - 1, 1 + (m.sheets.bit_length() - 1))
            self.assertTrue(verify(index.snapshot(), overlay.defects, make_certificate(index, overlay)))

    def test_reflection_fixed_points_and_signed_weights(self):
        for W in (1, 2, 3, 8, 9, 12, 30):
            for a in range(W):
                m = Model(1, W, 2, (Edge(0, 0, -1, a),),
                          (Weight(0, 0, W, (-1, 2)), Weight(0, 0, 1, (3, -4))))
                self.assert_oracle(BulkIndex(m), all_pairs=True)

    def test_representatives_avoid_touched_orbits(self):
        m = Model(1, 100, 1, (), (Weight(0, 0, 100, (1,)),))
        index = BulkIndex(m)
        overlay = SparseOverlay(index)
        for x in range(50):
            overlay.add(Defect(0, x, 0, x, (1,)))
        self.assertEqual(overlay.representative((1,)), (0, 50))
        self.assertEqual(overlay.weight(*overlay.representative((2,))), (2,))
        self.assertIsNone(overlay.representative((10,)))
        self.assert_oracle(index, overlay)

    def test_no_weights_zero_histogram(self):
        m = Model(3, 91, 4)
        index = BulkIndex(m)
        self.assertEqual(index.histogram, Counter({(0, 0, 0, 0): 273}))
        overlay = SparseOverlay(index)
        overlay.add(Defect(0, 0, 2, 90, (0, 0, 0, 0)))
        self.assertEqual(overlay.histogram, Counter({(0, 0, 0, 0): 272}))

    def test_huge_binary_fibres(self):
        W = 1 << 24000
        m = Model(2, W, 3, (Edge(0, 1, -1, W - 9), Edge(0, 0, 1, 1 << 23900),
                            Edge(1, 1, -1, 18)),
                  (Weight(0, 0, W, (1, 0, 0)), Weight(1, 13, W - 21, (0, 1, -1))))
        index = BulkIndex(m)
        overlay = SparseOverlay(index)
        overlay.add(Defect(0, 0, 1, W - 1, (-1, 0, 0)))
        cert = make_certificate(index, overlay)
        encoded = json.loads(json.dumps(wire(cert)))
        self.assertTrue(verify(m, overlay.defects, encoded))
        self.assertLessEqual(len(overlay.histogram), 2 * len(m.weights) + 4)
        for val in overlay.histogram:
            self.assertEqual(overlay.weight(*overlay.representative(val)), val)

    def test_sharp_event_chain(self):
        W = 1 << 12
        index = BulkIndex(Model(1, W, 1, (), (Weight(0, 0, W, (1,)),)))
        changes = 0
        for j in range(11, -1, -1):
            changes += index.add_root_map(0, 1, 1 << j)
            for _ in range(4):
                self.assertFalse(index.add_root_map(0, 1, 1 << j))
        changes += index.add_root_map(0, -1, 0)
        self.assertEqual(changes, 13)
        self.assertEqual(index.component_count, 1)

    def test_sharp_scalar_profile_bound(self):
        for K in range(1, 31):
            d = 4 * K + 4
            W = 5 * d
            weights = tuple(Weight(0, d-j, 4*d+K+j+1, (1,))
                            for j in range(1, K+1))
            m = Model(1, W, 1, (Edge(0, 0, 1, d), Edge(0, 0, -1, 0)), weights)
            i = BulkIndex(m)
            expected = {(3*K,), (4*K,)} | {(z,) for z in range(6*K, 8*K+1)}
            self.assertEqual(set(i.histogram), expected)
            self.assertEqual(len(i.histogram), 2*K+3)
            self.assert_oracle(i)

    def test_cancelled_rebase_stays_stale(self):
        m = Model(1, 32, 1, (), (Weight(0, 0, 32, (1,)),))
        i = BulkIndex(m)
        o = SparseOverlay(i)
        for j in range(4):
            o.add(Defect(0, j, 0, j+4, (-1,)))
        i.add_root_map(0, 1, 16)
        calls = 0
        def check():
            nonlocal calls
            calls += 1
            if calls == 3:
                raise TimeoutError('cancelled during replay')
        i.check = check
        with self.assertRaises(TimeoutError):
            o.rebase()
        with self.assertRaises(RuntimeError):
            _ = o.histogram
        i.check = None
        o.rebase()
        self.assert_oracle(i, o)

    def test_attachment_information_matters(self):
        m = Model(1, 8, 1, (), (Weight(0, 0, 8, (1,)),))
        a, b = SparseOverlay(BulkIndex(m)), SparseOverlay(BulkIndex(m))
        a.add(Defect(0, 0, 0, 0, (-1,)))
        b.add(Defect(0, 0, 0, 1, (-1,)))
        self.assertEqual(a.histogram, Counter({(1,): 7, (0,): 1}))
        self.assertEqual(b.histogram, Counter({(1,): 7}))


class GuardTests(unittest.TestCase):
    def test_exhaustive_split_guard(self):
        count = 0
        for W in range(1, 31):
            for s in (-1, 1):
                for a in range(W):
                    e = Edge(0, 1, s, a)
                    pieces = split_edge(e, W)
                    m = from_pairing_groups(2, W, 1, [pieces])
                    self.assertEqual(m.edges, (e,))
                    self.assertLessEqual(len(pieces), 2)
                    count += 1
        self.assertEqual(count, 930)

    def test_gap_rejected(self):
        p = split_edge(Edge(0, 1, 1, 3), 10)
        p.pop()
        with self.assertRaises(UnsupportedModel):
            from_pairing_groups(2, 10, 1, [p])

    def test_overlap_rejected(self):
        p = split_edge(Edge(0, 1, 1, 3), 10)
        p.append(p[0].copy())
        with self.assertRaises(UnsupportedModel):
            from_pairing_groups(2, 10, 1, [p])

    def test_conflicting_map_rejected(self):
        p = split_edge(Edge(0, 1, 1, 3), 10)
        p[1]["image_start"] += 1
        with self.assertRaises(UnsupportedModel):
            from_pairing_groups(2, 10, 1, [p])

    def test_wrapping_piece_rejected(self):
        p = [dict(u=0, v=1, sign=1, start=0, stop=10, image_start=3)]
        with self.assertRaises(UnsupportedModel):
            from_pairing_groups(2, 10, 1, [p])

    def test_subdivided_full_rule_accepted(self):
        p = [dict(u=0, v=0, sign=-1, start=a, stop=a + 1, image_start=9 - a)
             for a in range(10)]
        m = from_pairing_groups(1, 10, 1, [p])
        self.assertEqual(m.edges, (Edge(0, 0, -1, 9),))


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.m = Model(3, 24, 2, (Edge(0, 1, -1, 5), Edge(1, 2, 1, 2),
                                  Edge(2, 0, 1, 3), Edge(0, 0, 1, 8)),
                       (Weight(0, 0, 24, (1, 0)), Weight(1, 3, 20, (0, 2))))
        self.i = BulkIndex(self.m)
        self.o = SparseOverlay(self.i)
        self.o.add(Defect(0, 0, 2, 17, (-1, 0)))
        self.c = make_certificate(self.i, self.o)

    def test_valid_and_hex_roundtrip(self):
        self.assertTrue(verify(self.m, self.o.defects, self.c))
        self.assertTrue(verify(wire(self.m.as_dict()), [wire(vars(e)) for e in self.o.defects], wire(self.c)))

    def test_source_weight_tampering(self):
        m = self.m.as_dict()
        m["weights"][0] = dict(v=0, start=0, stop=24, value=(2, 0))
        with self.assertRaises(ValueError):
            verify(m, self.o.defects, self.c)

    def test_omitted_defect(self):
        with self.assertRaises(ValueError):
            verify(self.m, [], self.c)

    def test_forest_sign_tampering(self):
        c = copy.deepcopy(self.c)
        c["signs"][1] *= -1
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_bezout_tampering(self):
        c = copy.deepcopy(self.c)
        c["components"][0]["gcd_witnesses"][0][1] += 1
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_divisor_tampering(self):
        c = copy.deepcopy(self.c)
        c["components"][0]["divisor"] += 1
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_histogram_tampering(self):
        c = copy.deepcopy(self.c)
        c["histogram"][0]["multiplicity"] += 1
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_component_histogram_tampering(self):
        c = copy.deepcopy(self.c)
        c["components"][0]["histogram"][0]["weight"][0] += 1
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_bool_alias_rejected(self):
        c = copy.deepcopy(self.c)
        c["signs"][0] = True
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_duplicate_histogram_entry(self):
        c = copy.deepcopy(self.c)
        c["histogram"].append(c["histogram"][0].copy())
        with self.assertRaises(ValueError):
            verify(self.m, self.o.defects, c)

    def test_checker_independent_of_producer(self):
        import affine_orbits.core as core
        old = core.BulkIndex.__init__
        def forbidden(*args, **kwargs):
            raise RuntimeError("producer disabled")
        core.BulkIndex.__init__ = forbidden
        try:
            self.assertTrue(verify(self.m, self.o.defects, self.c))
        finally:
            core.BulkIndex.__init__ = old


class API(unittest.TestCase):
    def test_defensive_histogram_copy(self):
        i = BulkIndex(Model(1, 8, 1))
        h = i.histogram
        h.clear()
        self.assertEqual(i.component_count, 8)
        self.assertEqual(sum(i.histogram.values()), 8)

    def test_stale_overlay_and_rebase(self):
        i = BulkIndex(Model(1, 8, 1))
        o = SparseOverlay(i)
        o.add(Defect(0, 0, 0, 1, (2,)))
        self.assertFalse(i.add_root_map(0, 1, 0))
        self.assertEqual(o.component_count, 7)
        self.assertTrue(i.add_root_map(0, 1, 2))
        with self.assertRaises(RuntimeError):
            o.weight(0, 0)
        o.rebase()
        self.assertEqual(o.component_count, 1)
        self.assertEqual(o.weight(0, 0), (2,))

    def test_input_boolean_rejected(self):
        for bad in (True, "12", 2.0):
            with self.assertRaises(ValueError):
                BulkIndex(dict(vertices=1, sheets=bad, dimension=1))

    def test_invalid_dimensions_and_points(self):
        with self.assertRaises(ValueError):
            BulkIndex(Model(1, 0, 1))
        i = BulkIndex(Model(1, 8, 1))
        for u, x in ((-1, 0), (1, 0), (0, 8), (0, True)):
            with self.assertRaises(ValueError):
                i.key(u, x)
        with self.assertRaises(ValueError):
            SparseOverlay(i).add(Defect(0, 0, 0, 1, (1, 2)))

    def test_callbacks_propagate(self):
        class Stop(Exception):
            pass
        def check():
            raise Stop()
        with self.assertRaises(Stop):
            BulkIndex(Model(1, 8, 1), check=check)

    def test_cancelled_update_is_atomic(self):
        class Stop(Exception):
            pass
        i = BulkIndex(Model(1, 1024, 1, (), tuple(Weight(0, x, x + 1, (x,)) for x in range(20))))
        old_h, old_s = i.histogram, i.snapshot()
        calls = 0
        def check():
            nonlocal calls
            calls += 1
            if calls == 5:
                raise Stop()
        i.check = check
        with self.assertRaises(Stop):
            i.add_root_map(0, 1, 16)
        self.assertEqual(i.histogram, old_h)
        self.assertEqual(i.snapshot(), old_s)


if __name__ == "__main__":
    unittest.main()
