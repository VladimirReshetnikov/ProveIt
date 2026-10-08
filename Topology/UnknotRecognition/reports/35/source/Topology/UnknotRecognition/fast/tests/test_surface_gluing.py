"""Topology, marking and seam-certificate tests against explicit lifted graphs."""

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import io
from itertools import product
import json
from pathlib import Path
import random
import tempfile
import unittest

from fastunknot.integer_codec import json_safe
from fastunknot.surface_gluing import GluedCoverIndex, assemble_cover, main, verify_gauge_certificate
from gluing_research.fixtures import (annulus_chain, genus_two, klein_seam, piece,
                                      projective_cap, random_assemblies, seam)
from gluing_research.oracle import (compatible, compressed_records, expanded_assembly,
                                    rooted_isomorphism)


class SurfaceGluingTests(unittest.TestCase):
    comparisons = 0
    point_checks = 0

    def compare(self, raw, *, mark_checks=False):
        index = GluedCoverIndex(raw)
        summary = index.summary
        oracle = expanded_assembly(raw)
        self.assertEqual(compressed_records(summary), oracle['records'], raw)
        self.assertTrue(verify_gauge_certificate(raw, index.gauge_certificate))
        self.assertEqual(summary['base_component_count'], len(oracle['groups']))
        self.assertEqual(summary['component_count'], len(oracle['components']))
        self.assertTrue(all(len(base['families']) <= 3 for base in summary['base_components']))
        n = raw['sheets']
        by_key, by_component = {}, {}
        for vertex, component in enumerate(oracle['component_of']):
            key = index.component_key(vertex // n, vertex % n)
            self.assertEqual(by_key.setdefault(key, component), component)
            self.assertEqual(by_component.setdefault(component, key), key)
        for (v, b), cycles in oracle['port_cycles'].items():
            seen = set()
            for cycle in cycles:
                query = index.port_lift_key(v, b, cycle[0])
                self.assertNotIn(query['key'], seen)
                seen.add(query['key'])
                self.assertEqual(query['covering_degree'], len(cycle))
                for x in cycle:
                    self.assertEqual(index.port_lift_key(v, b, x), query)
                if query['kind'] == 'seam':
                    e = query['seam']
                    reverse = [v, b] == raw['seams'][e]['right']
                    transported = index.transport_across_seam(e, cycle[0], reverse=reverse)
                    u, c = transported['port']
                    mate = index.port_lift_key(u, c, transported['sheet'])
                    self.assertEqual(query['key'], mate['key'])
                    self.assertEqual(query['component_key'], mate['component_key'])
                else:
                    self.assertEqual(index.boundary_lift_key(v, b, cycle[0]), query)
        if mark_checks:
            self.check_marks(raw, index, oracle)
        type(self).comparisons += 1

    def check_marks(self, raw, index, oracle):
        n = raw['sheets']
        for v in range(len(raw['pieces'])):
            for x, y in product(range(n), repeat=2):
                literal = rooted_isomorphism(raw, oracle, (v, x), (v, y))
                comp = oracle['component_of'][v * n + x]
                members = oracle['components'][comp]
                for z in members:
                    point = [z // n, z % n]
                    answer = index.transport_point((v, x), (v, y), point)
                    expected = None if literal is None else [z // n, literal[z] % n]
                    self.assertEqual(answer, expected, (raw, (v, x), (v, y), point))
                    left = index.marked_signature(v, x, [(v, x), point])
                    # Compare every second target mark over the same basepoint.
                    target_comp = oracle['component_of'][v * n + y]
                    for target_z in oracle['components'][target_comp]:
                        if target_z // n != z // n:
                            continue
                        right = index.marked_signature(v, y, [(v, y), (z // n, target_z % n)])
                        self.assertEqual(left == right,
                                         literal is not None and literal[z] == target_z)
                        type(self).point_checks += 1

    def test_all_self_sewn_annuli_through_six_sheets(self):
        for n in range(1, 7):
            atoms = list(product((-1, 1), range(n)))
            for g, a, epsilon in product(atoms, atoms, (-1, 1)):
                raw = dict(sheets=n, pieces=[piece(maps=(g,))],
                           seams=[seam((0, 0), (0, 1), epsilon, a)])
                if compatible(raw, raw['seams'][0]):
                    self.compare(raw)

    def test_all_sewn_pants_through_five_sheets(self):
        # h=A*g^epsilon*A^-1 follows from A*g=h^epsilon*A.
        for n in range(1, 6):
            atoms = list(product((-1, 1), range(n)))
            for g, a, epsilon in product(atoms, atoms, (-1, 1)):
                gs, gc = g
                if epsilon == -1:
                    gc = -gs * gc
                as_, ac = a
                h = gs, (as_ * gc + (1 - gs) * ac) % n
                raw = dict(sheets=n, pieces=[piece(True, 0, 3, (g, h))],
                           seams=[seam((0, 0), (0, 1), epsilon, a)])
                self.assertTrue(compatible(raw, raw['seams'][0]))
                self.compare(raw)

    def test_spheres_projective_planes_and_disconnected_bases(self):
        for n in range(1, 10):
            for sign, shift, epsilon in product((-1, 1), range(n), (-1, 1)):
                disk = piece(True, 0, 1, ())
                raw = dict(sheets=n, pieces=[disk, disk],
                           seams=[seam((0, 0), (1, 0), epsilon, (sign, shift))])
                self.compare(raw)
            self.compare(projective_cap(n, 0))
            self.compare(projective_cap(n, 1))
        raw = dict(sheets=6, pieces=[piece(), piece(), piece(True, 0, 1, ())],
                   seams=[seam((0, 0), (0, 1), 1, (-1, 0))])
        self.compare(raw)
        self.assertEqual(assemble_cover(raw)['base_component_count'], 3)

    def test_seeded_mixed_surfaces_and_seams(self):
        for raw in random_assemblies(500):
            self.compare(raw)

    def test_labelled_graph_transport_and_markings(self):
        for n in range(1, 5):
            for shift in (0, 1):
                self.compare(klein_seam(n, shift), mark_checks=True)
                self.compare(projective_cap(n, shift), mark_checks=True)
                self.compare(annulus_chain(n, 3, shift), mark_checks=True)
            self.compare(genus_two(n), mark_checks=True)

    def test_huge_closed_topology_and_seam_provenance(self):
        for bits in (1, 17, 2048, 24000):
            n = 1 << bits
            left = GluedCoverIndex(klein_seam(n, 0))
            right = GluedCoverIndex(klein_seam(n, 1))
            self.assertEqual(left.summary['component_count'], 2)
            self.assertEqual(right.summary['component_count'], 1)
            self.assertEqual([(f['cover_degree'], f['orientable'], f['genus'])
                              for f in left.summary['base_components'][0]['families']],
                             [(n // 2, False, 2), (n // 2, False, 2)])
            self.assertEqual([(f['cover_degree'], f['orientable'], f['genus'])
                              for f in right.summary['base_components'][0]['families']],
                             [(n, True, 1)])
            self.assertNotEqual(left.marked_signature(0, 0), right.marked_signature(0, 0))
            for index in (left, right):
                self.assertTrue(verify_gauge_certificate(index.summary['normalized_input'],
                                                       index.gauge_certificate))
                self.assertEqual(index.summary['base_components'][0]['base_surface'],
                                 dict(orientable=False, genus=2, boundary_components=0,
                                      euler_characteristic=0))
        cap = assemble_cover(projective_cap(1 << 24000))['base_components'][0]
        self.assertEqual(len(cap['families']), 3)
        self.assertEqual(cap['families'][0]['multiplicity'], (1 << 23999) - 1)
        self.assertEqual(cap['families'][0]['genus'], 0)
        self.assertTrue(cap['families'][0]['orientable'])
        self.assertTrue(all(f['genus'] == 1 and not f['orientable']
                            for f in cap['families'][1:]))

    def test_huge_tree_gauges_and_genus(self):
        n = 1 << 20000
        for shift in (0, 1):
            raw = annulus_chain(n, 64, shift)
            index = GluedCoverIndex(raw)
            self.assertTrue(verify_gauge_certificate(raw, index.gauge_certificate))
            self.assertEqual(index.summary['component_count'], 2 if shift == 0 else 1)
            for record in index.gauge_certificate:
                sign, a = record['map']['sign'], record['map']['shift']
                v = record['piece']
                for x in (0, 1, n - 1):
                    point = (sign * x + a) % n
                    self.assertEqual(index.to_root(v, point), (0, x))
                    self.assertEqual(index.component_key(v, point), index.component_key(0, x))
        base = assemble_cover(genus_two(n))['base_components'][0]
        self.assertEqual(base['base_surface']['genus'], 2)
        self.assertEqual(len(base['families']), 3)
        for family in base['families']:
            self.assertEqual(family['genus'], family['cover_degree'] + 1)
            self.assertTrue(family['orientable'])

    def test_relabeling_gauges_and_seam_direction_reversal(self):
        rng = random.Random(911)
        for raw in random_assemblies(50, seed=882):
            original = assemble_cover(raw)
            n = raw['sheets']
            changed = deepcopy(raw)
            gauges = [(rng.choice((-1, 1)), rng.randrange(n)) for _ in raw['pieces']]
            for v, item in enumerate(changed['pieces']):
                s, a = gauges[v]
                for m in item['monodromy']:
                    m['shift'] = (s * m['shift'] + (1 - m['sign']) * a) % n
            for item in changed['seams']:
                u, v = item['left'][0], item['right'][0]
                su, au = gauges[u]
                sv, av = gauges[v]
                s, a = item['map']['sign'], item['map']['shift']
                item['map'] = dict(sign=sv * s * su,
                                   shift=(sv * (a - s * su * au) + av) % n)
            self.assertEqual(compressed_records(original), compressed_records(assemble_cover(changed)))
            for item in changed['seams']:
                item['left'], item['right'] = item['right'], item['left']
                item['map']['shift'] = -item['map']['sign'] * item['map']['shift']
            self.assertEqual(compressed_records(original), compressed_records(assemble_cover(changed)))

    def test_certificate_replay_and_corruption(self):
        raw = annulus_chain(42, 8, 1)
        index = GluedCoverIndex(raw)
        certificate = index.gauge_certificate
        self.assertTrue(verify_gauge_certificate(raw, json_safe(certificate)))
        mutations = []
        for position, field, value in [(0, 'root', 1), (0, 'orientation_bit', 1),
                                       (1, 'parent', 1), (1, 'seam', 6),
                                       (1, 'reverse', True), (1, 'piece', 2),
                                       (1, 'orientation_bit', True)]:
            bad = deepcopy(certificate)
            bad[position][field] = value
            mutations.append(bad)
        bad = deepcopy(certificate)
        bad[1]['map']['shift'] += 1
        mutations.append(bad)
        mutations.extend((certificate[:-1], 'not a certificate', [{}] * 8))
        for bad in mutations:
            self.assertFalse(verify_gauge_certificate(raw, bad), bad)
        # A different, verified tree may legitimately use another root.
        tree = dict(sheets=7, pieces=[piece(), piece()],
                    seams=[seam((0, 1), (1, 0), -1, (1, 3))])
        certificate = [dict(piece=0, root=1, parent=1, seam=0, reverse=True,
                            map=dict(sign=1, shift=4), orientation_bit=0),
                       dict(piece=1, root=1, parent=None, seam=None, reverse=False,
                            map=dict(sign=1, shift=0), orientation_bit=0)]
        self.assertTrue(verify_gauge_certificate(tree, certificate))

    def test_invalid_seams_and_queries(self):
        raw = klein_seam(6)
        mutations = []
        for path, value in [(('sheets',), 0), (('sheets',), True),
                             (('pieces',), []), (('seams', 0, 'direction'), 0),
                             (('seams', 0, 'map', 'sign'), True),
                             (('seams', 0, 'map', 'sign'), 1),
                             (('seams', 0, 'right'), [0, 0]),
                             (('seams', 0, 'right'), [1, 0])]:
            bad = deepcopy(raw)
            current = bad
            for key in path[:-1]:
                current = current[key]
            current[path[-1]] = value
            mutations.append(bad)
        mutations.append({**raw, 'extra': 0})
        bad = deepcopy(raw)
        bad['seams'].append(deepcopy(bad['seams'][0]))
        mutations.append(bad)
        for bad in mutations:
            with self.assertRaises(ValueError):
                GluedCoverIndex(bad)
        index = GluedCoverIndex(raw)
        for point in [(-1, 0), (0, 6), (True, 0), (1, 0), (0, 0.5)]:
            with self.assertRaises(ValueError):
                index.component_key(*point)
        with self.assertRaises(ValueError):
            index.boundary_lift_key(0, 0, 0)
        with self.assertRaises(ValueError):
            index.marked_signature(0, 0, [(0, 1)])
        with self.assertRaises(ValueError):
            index.transport_point((0, 0), (0, 1), (0, 1))
        with self.assertRaises(ValueError):
            GluedCoverIndex(raw, check=3)

    def test_point_base_labels_and_defensive_copies(self):
        raw = annulus_chain(8, 2)
        index = GluedCoverIndex(raw)
        root1 = index.gauge_certificate[1]['map']
        sheet = root1['shift'] % 8
        self.assertNotEqual(index.marked_signature(0, 0, [(0, 0)]),
                            index.marked_signature(0, 0, [(1, sheet)]))
        with self.assertRaises(ValueError):
            index.transport_point((0, 0), (1, sheet), (0, 0))
        saved = index.summary
        saved['normalized_input']['pieces'].clear()
        saved['base_components'][0]['families'].clear()
        saved['gauge_certificate'][0]['map']['shift'] = 1
        self.assertTrue(index.summary['base_components'][0]['families'])
        self.assertEqual(index.to_root(0, 0), (0, 0))
        raw['pieces'].clear()
        self.assertEqual(len(index.summary['normalized_input']['pieces']), 2)

    def test_iterated_seams_preserve_point_coordinates(self):
        raw = annulus_chain(14, 3, 1)
        all_seams = raw.pop('seams')
        raw['seams'] = []
        original = GluedCoverIndex(raw)
        partial = original.with_seams(all_seams[:2])
        closed = partial.with_seams(all_seams[2:])
        self.assertEqual(original.summary['base_component_count'], 3)
        self.assertEqual(partial.summary['base_component_count'], 1)
        self.assertEqual(partial.summary['base_components'][0]['base_surface']['boundary_components'], 2)
        self.assertEqual(closed.summary['component_count'], 1)
        self.assertEqual(closed.summary['base_components'][0]['families'][0]['genus'], 1)
        self.assertEqual(original.port_lift_key(0, 0, 0)['kind'], 'boundary')
        self.assertEqual(partial.port_lift_key(0, 0, 0)['kind'], 'boundary')
        self.assertEqual(closed.port_lift_key(0, 0, 0)['kind'], 'seam')
        for index in (original, partial, closed):
            for v in range(3):
                for x in (0, 1, 13):
                    self.assertEqual(index.transport_point((v, x), (v, x), (v, x)), [v, x])
        with self.assertRaises(ValueError):
            closed.with_seams(all_seams[:1])

    def test_cooperative_cancellation(self):
        class Stop(Exception):
            pass
        raw = annulus_chain(1 << 1000, 8, 1)
        total = 0
        def count():
            nonlocal total
            total += 1
        GluedCoverIndex(raw, check=count)
        self.assertGreater(total, 50)
        for limit in (1, 2, 10, total // 2, total):
            ticks = 0
            def check():
                nonlocal ticks
                ticks += 1
                if ticks >= limit:
                    raise Stop
            with self.assertRaises(Stop):
                GluedCoverIndex(raw, check=check)
        allowed = True
        def check():
            if not allowed:
                raise Stop
        index = GluedCoverIndex(raw, check=check)
        allowed = False
        for query in (lambda: index.summary, lambda: index.component_key(0, 0),
                      lambda: index.marked_signature(0, 0),
                      lambda: verify_gauge_certificate(raw, [], check=check)):
            with self.assertRaises(Stop):
                query()

    def test_hexadecimal_cli_roundtrip_and_deadline(self):
        raw = annulus_chain(1 << 24000, 3, 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'assembly.json'
            path.write_text(json.dumps(json_safe(raw)))
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(main([str(path), '--port', '0', '0', '0']), 0)
            answer = json.loads(output.getvalue())
            self.assertEqual(answer['component_count'], 1)
            self.assertTrue(verify_gauge_certificate(raw, answer['gauge_certificate']))
            self.assertEqual(answer['port_query']['kind'], 'seam')
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as failure:
                main([str(path), '--seconds', '0'])
            self.assertEqual(failure.exception.code, 2)

    @classmethod
    def tearDownClass(cls):
        print(f'Surface-gluing expanded topology comparisons: {cls.comparisons}; '
              f'ordered marking checks: {cls.point_checks}')


if __name__ == '__main__':
    unittest.main(verbosity=2)
