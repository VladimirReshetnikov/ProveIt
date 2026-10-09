"""Source-bound topology, local geometry and hostile exterior face pairings."""
from copy import deepcopy
import importlib.util
from itertools import permutations
import random
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.diagram_exterior import diagram_exterior, _corner_triangulation
from fastunknot.diagram_exterior_verify import verify_diagram_exterior, _local_geometry
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)


def examples():
    yield Diagram.from_pd([])
    for strands, word in ((2, [1]), (2, [-1]), (2, [1, 1, -1]),
                          (2, [1, 1, 1]), (3, [1, -2, 1, -2]),
                          (4, [1, 2, 3])):
        yield Diagram.from_braid(strands, word)


class DiagramExteriorTests(unittest.TestCase):
    def test_finite_manifold_and_independent_checker(self):
        for source in examples():
            variants = (source, source.mirror(), Diagram.from_pd(
                [row[2:] + row[:2] for row in reversed(source.pd)]))
            for diagram in variants:
                raw = diagram_exterior(diagram)
                self.assertEqual(len(raw['tetrahedra']), 80*max(1, diagram.crossings))
                with patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError), \
                     patch('fastunknot.diagram_exterior._template', side_effect=AssertionError), \
                     patch('fastunknot.diagram_exterior._corner_triangulation', side_effect=AssertionError):
                    self.assertTrue(verify_diagram_exterior(diagram, raw))
                prepared = _prepare(raw, lambda: None)
                self.assertEqual(len(prepared['boundary_faces']), 8*max(1, diagram.crossings))

    def test_convex_template_volume_and_face_multiplicity(self):
        cells = _local_geometry()
        faces, volume = {}, 0
        for cell in cells:
            matrix = [[p[v] - cell[0][v] for v in range(3)] for p in cell[1:]]
            determinant = 0
            for p in permutations(range(3)):
                sign = (-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
                determinant += sign*matrix[0][p[0]]*matrix[1][p[1]]*matrix[2][p[2]]
            self.assertNotEqual(determinant, 0)
            volume += abs(determinant)
            for f in range(4):
                key = tuple(sorted(p for v, p in enumerate(cell) if v != f))
                faces[key] = faces.get(key, 0) + 1
        self.assertEqual(volume, 1600)  # 12^3 * (1 - 2/3^3).
        self.assertEqual(sum(count == 1 for count in faces.values()), 20)
        self.assertEqual(sum(count == 2 for count in faces.values()), 30)
        self.assertTrue(all(count in (1, 2) for count in faces.values()))

    def test_every_face_mutation_and_wrong_source_rejected(self):
        diagram = Diagram.from_braid(2, [1])
        raw = diagram_exterior(diagram)
        for t, row in enumerate(raw['tetrahedra']):
            for f, record in enumerate(row):
                bad = deepcopy(raw)
                bad['tetrahedra'][t][f] = (dict(tetrahedron=t, permutation=[0, 1, 2, 3])
                                           if record is None else None)
                self.assertFalse(verify_diagram_exterior(diagram, bad))
        unknot = Diagram.from_braid(2, [1, 1, -1])
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        self.assertFalse(verify_diagram_exterior(unknot, diagram_exterior(trefoil)))
        bad = deepcopy(raw)
        t, f = next((t, f) for t, row in enumerate(bad['tetrahedra'])
                    for f, record in enumerate(row) if record is not None)
        record = bad['tetrahedra'][t][f]
        u, p = record['tetrahedron'], record['permutation']
        g = p[f]
        a, b = [v for v in range(4) if v != f][:2]
        p[a], p[b] = p[b], p[a]
        bad['tetrahedra'][u][g]['permutation'] = [p.index(v) for v in range(4)]
        self.assertFalse(verify_diagram_exterior(diagram, bad))

    def test_schema_is_exact_and_source_is_revalidated(self):
        diagram = Diagram.from_pd([])
        raw = diagram_exterior(diagram)
        for bad in (None, [], {}, dict(raw, extra=1), {'tetrahedra': []},
                    {'tetrahedra': tuple(raw['tetrahedra'])}):
            self.assertFalse(verify_diagram_exterior(diagram, bad))
        for value in (True, -1, len(raw['tetrahedra']), 0.0, '0'):
            bad = deepcopy(raw)
            bad['tetrahedra'][0][1]['tetrahedron'] = value
            self.assertFalse(verify_diagram_exterior(diagram, bad))
        for value in ([False, 1, 2, 3], [0, 1, 2, 2], [0], (0, 1, 2, 3)):
            bad = deepcopy(raw)
            bad['tetrahedra'][0][1]['permutation'] = value
            self.assertFalse(verify_diagram_exterior(diagram, bad))
        invalid = Diagram(((0, 1, 2, 3),))
        self.assertFalse(verify_diagram_exterior(invalid, raw))
        with self.assertRaises(DiagramError):
            diagram_exterior(invalid)

    def test_cancellation_and_no_input_mutation(self):
        class Cancelled(Exception):
            pass
        class Stop:
            def __init__(self, limit): self.left = limit
            def __bool__(self): return False
            def __call__(self):
                self.left -= 1
                if self.left <= 0: raise Cancelled
        diagram = Diagram.from_braid(3, [1, -2, 1, -2])
        raw = diagram_exterior(diagram)
        before = deepcopy(raw)
        for limit in (1, 2, 10):
            with self.assertRaises(Cancelled): diagram_exterior(diagram, check=Stop(limit))
            with self.assertRaises(Cancelled): verify_diagram_exterior(diagram, raw, check=Stop(limit))
        self.assertEqual(raw, before)

    def test_native_disc_checker_accepts_source_geometry_but_rejects_vertex_link_as_meridian(self):
        diagram = Diagram.from_pd([])
        raw = diagram_exterior(diagram)
        prepared = _prepare(raw, lambda: None)
        t, f = prepared['boundary_faces'][0]
        v = next(v for v in range(4) if v != f)
        root = prepared['vertex_roots'][4*t+v]
        vector = [[int(prepared['vertex_roots'][4*t+v] == root) for v in range(4)] + [0, 0, 0]
                  for t in range(len(raw['tetrahedra']))]
        answer = normal_compressing_disk_count(raw, vector, record_certificate=True)
        self.assertTrue(verify_normal_disk_count_certificate(raw, vector, answer['certificate']))
        self.assertEqual(answer['compressing_disk_components'], 0)
        bad = deepcopy(answer['certificate'])
        bad['compressing_disk_components'] = 1
        self.assertFalse(verify_normal_disk_count_certificate(raw, vector, bad))

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional external control')
    def test_weeks_isomorphism_and_independent_solid_torus_controls(self):
        import regina
        from fastunknot.normal_surface import regina_pd
        from normal_orbit_research.fixtures import regina_triangulation
        for i, diagram in enumerate(examples()):
            link = regina.Link.fromPD(regina_pd(diagram)) if diagram.pd else regina.Link(1)
            ideal = regina_triangulation({'tetrahedra': _corner_triangulation(diagram, lambda: None)})
            self.assertIsNotNone(ideal.isIsomorphicTo(link.complement(False)))
            compact = regina_triangulation(diagram_exterior(diagram))
            self.assertTrue(compact.isValid())
            self.assertFalse(compact.isIdeal())
            compact.simplify()
            self.assertEqual(compact.isSolidTorus(), i not in (4, 5))


if __name__ == '__main__':
    unittest.main()
