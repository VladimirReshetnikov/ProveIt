"""Source binding and formal-boundary replay, including an all-region move."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_pachner32_verify import verify_normal_pachner32
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError


def _digest(source):
    return sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def selfattached_fixture():
    """A 2--3 expansion of the two-tetrahedron layered solid torus.

    All three tetrahedra belong to the formal bipyramid. Its six exterior
    triangles comprise two ambient boundary triangles and two selfattachment
    pairs. These literal arrays require no discovery producer at replay time.
    """
    def join(t, permutation):
        return dict(tetrahedron=t, permutation=permutation)
    source = dict(tetrahedra=[
        [join(1, [0, 2, 1, 3]), None, join(1, [0, 1, 3, 2]), join(2, [0, 1, 3, 2])],
        [join(0, [0, 2, 1, 3]), join(2, [2, 0, 3, 1]),
         join(2, [0, 1, 3, 2]), join(0, [0, 1, 3, 2])],
        [join(1, [1, 3, 0, 2]), None, join(0, [0, 1, 3, 2]), join(1, [0, 1, 3, 2])],
    ])
    successor = dict(tetrahedra=[
        [join(1, [1, 0, 3, 2]), None, None, join(1, [0, 1, 2, 3])],
        [join(1, [2, 3, 1, 0]), join(0, [1, 0, 3, 2]),
         join(1, [3, 2, 0, 1]), join(0, [0, 1, 2, 3])],
    ])
    certificate = dict(schema='pachner-32-v1', region=[
        dict(tetrahedron=t, vertices=row)
        for t, row in enumerate(([3, 4, 0, 1], [3, 4, 1, 2], [3, 4, 2, 0]))
    ])
    packet = dict(schema='normal-pachner-32-v1', source_sha256=_digest(source),
                  certificate=certificate, successor=successor)
    return source, packet


class NormalPachner32VerifyTests(unittest.TestCase):
    def test_all_region_selfattachments_are_preserved(self):
        source, packet = selfattached_fixture()
        self.assertTrue(verify_normal_pachner32(source, packet))
        for triangulation in (source, packet['successor']):
            prepared = _prepare(triangulation, lambda: None)
            self.assertEqual(prepared['vertices'], 1)
            self.assertEqual(len(prepared['boundary_faces']), 2)
        region = {r['tetrahedron']: r['vertices'] for r in packet['certificate']['region']}
        facets = {(t, f) for t, labels in region.items()
                  for f in range(4) if labels[f] in (3, 4)}
        self.assertEqual(len(facets), 6)
        attached = []
        for t, f in sorted(facets):
            record = source['tetrahedra'][t][f]
            if record is not None:
                target = (record['tetrahedron'], record['permutation'][f])
                self.assertIn(target, facets)
                attached.append(tuple(sorted(((t, f), target))))
        self.assertEqual(len(attached), 4)
        self.assertEqual(len(set(attached)), 2)

    def test_replay_uses_no_discovery_producer_and_does_not_mutate(self):
        source, packet = selfattached_fixture()
        saved = deepcopy((source, packet))
        with ExitStack() as stack:
            for module, name in [('pachner23', 'pachner_23'), ('pachner32', 'pachner_32'),
                                 ('normal_sector', 'build_sector_kernel'),
                                 ('normal_sector', 'sector_rays'),
                                 ('exact_lp', 'solve_nonnegative_kernel')]:
                stack.enter_context(patch('fastunknot.'+module+'.'+name,
                                          side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_pachner32(source, packet))
        self.assertEqual((source, packet), saved)

    def test_multiple_global_vertices_and_surviving_exterior_are_supported(self):
        from fastunknot.diagram import Diagram
        from fastunknot.diagram_exterior import diagram_exterior
        from fastunknot.pachner23 import pachner_23
        from fastunknot.pachner32 import pachner_32
        initial = diagram_exterior(Diagram.from_pd([]))
        source = pachner_23(initial, 0, 0)['triangulation']
        result = pachner_32(source, len(source['tetrahedra'])-3, [0, 1])
        packet = dict(schema='normal-pachner-32-v1', source_sha256=_digest(source),
                      certificate=result['certificate'], successor=result['triangulation'])
        self.assertGreater(_prepare(source, lambda: None)['vertices'], 1)
        self.assertTrue(verify_normal_pachner32(source, packet))
        self.assertEqual(_prepare(source, lambda: None)['vertices'],
                         _prepare(packet['successor'], lambda: None)['vertices'])
        changed = deepcopy(packet)
        t, f = next((t, f) for t, row in enumerate(changed['successor']['tetrahedra'][:-2])
                    for f, record in enumerate(row) if record is not None)
        changed['successor']['tetrahedra'][t][f] = None
        self.assertFalse(verify_normal_pachner32(source, changed))

    def test_strict_outer_schema_and_nonempty_exact_descent(self):
        source, packet = selfattached_fixture()
        bad_packets = [None, [], {}, dict(packet, extra=0)]
        for field in packet:
            bad = deepcopy(packet)
            del bad[field]
            bad_packets.append(bad)
        for field, value in [('schema', True), ('schema', 'pachner-32-v1'),
                             ('source_sha256', True), ('source_sha256', '0'*64),
                             ('certificate', None), ('successor', None),
                             ('successor', {'tetrahedra': []}), ('successor', source),
                             ('successor', {'tetrahedra': packet['successor']['tetrahedra'][:1]})]:
            bad_packets.append(dict(packet, **{field: value}))
        for bad in bad_packets:
            with self.subTest(packet=bad):
                self.assertFalse(verify_normal_pachner32(source, bad))
        for bad in (None, [], {}, {'tetrahedra': []}, dict(source, extra=0),
                    {'tetrahedra': tuple(source['tetrahedra'])}):
            self.assertFalse(verify_normal_pachner32(bad, packet))

    def test_strict_formal_region_and_label_binding(self):
        source, packet = selfattached_fixture()
        mutations = [('tetrahedron', True), ('tetrahedron', 0.0), ('tetrahedron', -1),
                     ('tetrahedron', 3), ('vertices', (3, 4, 0, 1)),
                     ('vertices', [3, 4, False, 1]), ('vertices', [3, 4, 0.0, 1]),
                     ('vertices', [3, 4, 0, 0]), ('vertices', [3, 4, 0, 5]),
                     ('vertices', [0, 1, 2, 3]), ('vertices', [4, 3, 0, 1]), ('extra', 1)]
        for field, value in mutations:
            bad = deepcopy(packet)
            bad['certificate']['region'][0][field] = value
            with self.subTest(field=field, value=value):
                self.assertFalse(verify_normal_pachner32(source, bad))
        for change in (dict(schema=True), dict(schema='wrong'), dict(extra=0),
                       dict(region=[]), dict(region=packet['certificate']['region']*2)):
            bad = deepcopy(packet)
            bad['certificate'].update(change)
            self.assertFalse(verify_normal_pachner32(source, bad))
        bad = deepcopy(packet)
        bad['certificate']['region'][1] = deepcopy(bad['certificate']['region'][0])
        self.assertFalse(verify_normal_pachner32(source, bad))

    def test_source_and_successor_face_records_are_fully_validated(self):
        source, packet = selfattached_fixture()
        for which in ('source', 'successor'):
            raw = source if which == 'source' else packet['successor']
            for t, row in enumerate(raw['tetrahedra']):
                for f, record in enumerate(row):
                    if record is None:
                        continue
                    for value in (None, dict(record, tetrahedron=True),
                                  dict(record, permutation=[False, 1, 2, 3]),
                                  dict(record, extra=0)):
                        before, bad = deepcopy((source, packet))
                        target = before if which == 'source' else bad['successor']
                        target['tetrahedra'][t][f] = value
                        # Rebind malformed sources to exercise manifold validation,
                        # rather than merely a digest mismatch.
                        bad['source_sha256'] = _digest(before)
                        self.assertFalse(verify_normal_pachner32(before, bad))
        # Relabelled manifolds are not interchangeable with literal proof inputs.
        changed = deepcopy(source)
        changed['tetrahedra'].reverse()
        for row in changed['tetrahedra']:
            for record in row:
                if record is not None:
                    record['tetrahedron'] = 2-record['tetrahedron']
        _prepare(changed, lambda: None)
        self.assertFalse(verify_normal_pachner32(changed, packet))
        rebound = dict(packet, source_sha256=_digest(changed))
        self.assertFalse(verify_normal_pachner32(changed, rebound))

    def test_every_callback_exception_preserves_identity_inside_legacy_replay(self):
        source, packet = selfattached_fixture()
        calls = [0]
        def count():
            calls[0] += 1
        self.assertTrue(verify_normal_pachner32(source, packet, check=count))
        total = calls[0]
        class CallerStop(BaseException):
            pass
        for error_type in (NormalOrbitError, ValueError, TypeError, KeyError,
                           IndexError, AttributeError, OverflowError, RuntimeError,
                           KeyboardInterrupt, SystemExit, CallerStop):
            for stop in (1, 4, total//2, total):
                calls[0] = 0
                error = error_type('caller interruption')
                def cancel():
                    count()
                    if calls[0] == stop:
                        raise error
                with self.subTest(error=error_type, stop=stop):
                    with self.assertRaises(error_type) as raised:
                        verify_normal_pachner32(source, packet, check=cancel)
                    self.assertIs(raised.exception, error)
        malformed = deepcopy(source)
        malformed['tetrahedra'][0] = None
        packet['source_sha256'] = _digest(malformed)
        calls[0] = 0
        error = NormalOrbitError('caller inside malformed-source validation')
        def cancel_malformed():
            count()
            if calls[0] == 4:
                raise error
        with self.assertRaises(NormalOrbitError) as raised:
            verify_normal_pachner32(malformed, packet, check=cancel_malformed)
        self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
