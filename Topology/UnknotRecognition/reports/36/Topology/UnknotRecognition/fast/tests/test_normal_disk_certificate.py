"""Normal-disc witnesses: exact topology, binary coordinates and tampering."""

from copy import deepcopy
from itertools import combinations, permutations
import importlib.util
import random
import unittest

from fastunknot.normal_disk_certificate import (
    NormalDiskError, _prepare, audit_normal_disk_certificate,
    normal_disk_certificate, verify_normal_disk_certificate,
)


def core():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]}, None, None,
    ]]}, [[1, 1, 0, 0, 0, 0, 1]]


def relabel(triangulation, coordinates, generator):
    size = len(coordinates)
    order = list(range(size))
    generator.shuffle(order)
    maps = [generator.sample(range(4), 4) for _ in range(size)]
    faces = [[None] * 4 for _ in range(size)]
    result_coordinates = [[0] * 7 for _ in range(size)]
    for t, row in enumerate(triangulation['tetrahedra']):
        mapping = maps[t]
        for f, record in enumerate(row):
            if record is not None:
                u, permutation = record['tetrahedron'], record['permutation']
                transformed = [0] * 4
                for v in range(4):
                    transformed[mapping[v]] = maps[u][permutation[v]]
                faces[order[t]][mapping[f]] = dict(tetrahedron=order[u],
                                                  permutation=transformed)
        for v in range(4):
            result_coordinates[order[t]][mapping[v]] = coordinates[t][v]
        for q in range(3):
            pair = {mapping[0], mapping[q + 1]}
            if 0 not in pair:
                pair = set(range(4)) - pair
            new_q = next(v for v in pair if v != 0) - 1
            result_coordinates[order[t]][4 + new_q] = coordinates[t][4 + q]
    return {'tetrahedra': faces}, result_coordinates


class NormalDiskCertificateTests(unittest.TestCase):
    def test_literal_one_tetrahedron_meridian(self):
        triangulation, coordinates = core()
        certificate = normal_disk_certificate(triangulation, coordinates)
        self.assertIsNotNone(certificate)
        self.assertTrue(verify_normal_disk_certificate(triangulation, certificate))
        result = audit_normal_disk_certificate(triangulation, certificate)
        self.assertEqual(result['status'], 'CERTIFIED_COMPRESSING_DISK')
        self.assertEqual((result['support_size'], result['rank'], result['rank_prime']),
                         (3, 2, 2))
        self.assertEqual(result['normal_disks'], 3)
        self.assertEqual(result['boundary_normal_arcs'], 6)
        self.assertIn('no correspondence with an input knot', result['trust'])

    def test_exponentially_many_discs_remain_encoded(self):
        from certificate_research.fixtures import fibonacci, layered_torus
        triangulation, coordinates = layered_torus(128)
        certificate = normal_disk_certificate(triangulation, coordinates)
        result = audit_normal_disk_certificate(triangulation, certificate)
        self.assertEqual(result['normal_disks'], fibonacci(133) - 5)
        self.assertGreater(result['normal_disks'], 10**26)
        self.assertEqual(result['rank'], 3 * 128 - 1)
        self.assertLess(result['maximum_coordinate_bits'], 100)

    def test_vertex_link_disc_has_inessential_boundary(self):
        triangulation, _ = core()
        coordinates = [[1, 1, 1, 1, 0, 0, 0]]
        self.assertIsNone(normal_disk_certificate(triangulation, coordinates))
        certificate = dict(version=1, normal_coordinates=coordinates, rank_prime=2)
        with self.assertRaisesRegex(NormalDiskError, 'coboundary'):
            audit_normal_disk_certificate(triangulation, certificate)

    def test_annulus_and_nonprimitive_vectors_are_rejected(self):
        triangulation, coordinates = core()
        for bad in ([[0, 0, 0, 0, 0, 1, 0]],
                    [[0, 0, 1, 1, 1, 0, 0]],
                    [[2 * value for value in coordinates[0]]]):
            self.assertIsNone(normal_disk_certificate(triangulation, bad))
            self.assertFalse(verify_normal_disk_certificate(
                triangulation, dict(version=1, normal_coordinates=bad, rank_prime=2)))

    def test_quadrilaterals_matching_and_integer_types(self):
        triangulation, coordinates = core()
        for index, value in ((0, 2), (4, 1), (0, -1), (0, True), (0, 1.0)):
            bad = deepcopy(coordinates)
            bad[0][index] = value
            self.assertFalse(verify_normal_disk_certificate(
                triangulation, dict(version=1, normal_coordinates=bad, rank_prime=2)))

    def test_rank_modulus_checked_before_elimination(self):
        triangulation, coordinates = core()
        certificate = normal_disk_certificate(triangulation, coordinates)
        for prime in (3, 5, 7, 11):
            certificate['rank_prime'] = prime
            self.assertTrue(verify_normal_disk_certificate(triangulation, certificate))
        for modulus in (0, 1, 4, 9, True, 2.0, 2**10000 - 1):
            certificate['rank_prime'] = modulus
            self.assertFalse(verify_normal_disk_certificate(triangulation, certificate))

    def test_face_pairing_and_schema_tampering(self):
        triangulation, coordinates = core()
        certificate = normal_disk_certificate(triangulation, coordinates)
        broken = deepcopy(triangulation)
        broken['tetrahedra'][0][1] = None
        self.assertFalse(verify_normal_disk_certificate(broken, certificate))
        broken = deepcopy(triangulation)
        broken['tetrahedra'][0][0]['permutation'] = [0, 1, 2, 3]
        self.assertFalse(verify_normal_disk_certificate(broken, certificate))
        for key, value in (('version', True), ('extra', 1),
                           ('normal_coordinates', [[1] * 6])):
            bad = deepcopy(certificate)
            bad[key] = value
            self.assertFalse(verify_normal_disk_certificate(triangulation, bad))
        self.assertFalse(verify_normal_disk_certificate({}, certificate))

    def test_ball_and_disconnected_input_rejected(self):
        _, coordinates = core()
        certificate = dict(version=1, normal_coordinates=coordinates, rank_prime=2)
        self.assertFalse(verify_normal_disk_certificate(
            {'tetrahedra': [[None] * 4]}, certificate))
        triangulation, coordinates = core()
        doubled = deepcopy(triangulation)
        second = deepcopy(triangulation['tetrahedra'][0])
        for record in second:
            if record is not None:
                record['tetrahedron'] = 1
        doubled['tetrahedra'].append(second)
        with self.assertRaisesRegex(NormalDiskError, 'not connected'):
            normal_disk_certificate(doubled, coordinates * 2)

    def test_local_and_global_relabelling(self):
        from certificate_research.fixtures import layered_torus
        generator = random.Random(817)
        original, coordinates = layered_torus(7)
        for _ in range(24):
            triangulation, changed = relabel(original, coordinates, generator)
            certificate = normal_disk_certificate(triangulation, changed)
            self.assertIsNotNone(certificate)
            self.assertTrue(verify_normal_disk_certificate(triangulation, certificate))

    def test_cancellation_is_not_swallowed(self):
        class Cancelled(RuntimeError):
            pass
        calls = 0

        def check():
            nonlocal calls
            calls += 1
            if calls == 5:
                raise Cancelled()
        triangulation, coordinates = core()
        certificate = normal_disk_certificate(triangulation, coordinates)
        with self.assertRaises(Cancelled):
            verify_normal_disk_certificate(triangulation, certificate, check=check)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_native_vertex_surface_crosscheck(self):
        import regina
        from certificate_research.fixtures import (export_surface, layered_torus,
                                                   regina_triangulation)
        checked = 0
        for size in range(1, 7):
            triangulation, _ = layered_torus(size)
            native = regina_triangulation(triangulation)
            for surface in regina.NormalSurfaces(native, regina.NormalCoords.Standard):
                result = normal_disk_certificate(triangulation, export_surface(surface))
                self.assertEqual(result is not None, surface.isCompressingDisc())
                checked += 1
        self.assertGreater(checked, 20)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_all_one_pair_face_gluings_against_native_validity(self):
        from certificate_research.fixtures import regina_triangulation
        for f, g in combinations(range(4), 2):
            for permutation in permutations(range(4)):
                if permutation[f] != g:
                    continue
                inverse = [permutation.index(v) for v in range(4)]
                faces = [None] * 4
                faces[f] = dict(tetrahedron=0, permutation=list(permutation))
                faces[g] = dict(tetrahedron=0, permutation=inverse)
                triangulation = {'tetrahedra': [faces]}
                native = regina_triangulation(triangulation)
                expected = (native.isValid() and not native.isIdeal()
                            and native.isOrientable() and native.isConnected()
                            and native.countBoundaryComponents() == 1
                            and native.boundaryComponent(0).eulerChar() == 0)
                try:
                    _prepare(triangulation, lambda: None)
                    actual = True
                except NormalDiskError:
                    actual = False
                self.assertEqual(actual, expected, (f, g, permutation))


if __name__ == '__main__':
    unittest.main()
