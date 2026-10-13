"""Strict geometry-only first-descent replay and hostile certificate controls."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import inspect
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_geometric_descent_verify import verify_normal_geometric_descent
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.pachner32_verify import verify_pachner_32


def _digest(source):
    return sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _packet(source, operations):
    """Construct specified moves for fixtures, without running any search."""
    from fastunknot.pachner23 import pachner_23
    from fastunknot.pachner32 import pachner_32
    current, steps = source, []
    for kind, tetrahedron, port in operations:
        answer = (pachner_23 if kind == 'up' else pachner_32)(current, tetrahedron, port)
        current = answer['triangulation']
        steps.append(dict(triangulation=current, certificate=answer['certificate']))
    return dict(schema='normal-geometric-descent-v1', source_sha256=_digest(source),
                steps=steps, successor=current)


def geometric_descent_fixture():
    from causal_research.fixtures import attach_gadgets
    source = attach_gadgets()['triangulation']
    return source, _packet(source, [('up', 1, 0), ('down', 1, [1, 2]), ('down', 1, [1, 2])])


def _elementary_replay(source, packet):
    for step in packet['steps']:
        certificate = step['certificate']
        verifier = verify_pachner_23 if certificate['schema'] == 'pachner-23-v1' else verify_pachner_32
        if not verifier(source, step['triangulation'], certificate):
            return False
        source = step['triangulation']
    return True


class NormalGeometricDescentVerifyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source, cls.packet = geometric_descent_fixture()
        from tests.test_normal_pachner32_verify import selfattached_fixture
        cls.small, old = selfattached_fixture()
        cls.direct = dict(schema='normal-geometric-descent-v1', source_sha256=_digest(cls.small),
                          steps=[dict(triangulation=old['successor'], certificate=old['certificate'])],
                          successor=old['successor'])

    def test_genuine_udd_with_multiple_vertices_and_unchanged_exterior(self):
        self.assertEqual(_prepare(self.source, lambda: None)['vertices'], 5)
        self.assertEqual([len(step['triangulation']['tetrahedra']) for step in self.packet['steps']], [8, 7, 6])
        self.assertTrue(_elementary_replay(self.source, self.packet))
        self.assertTrue(verify_normal_geometric_descent(self.source, self.packet))
        self.assertEqual(_prepare(self.packet['successor'], lambda: None)['vertices'], 5)

    def test_direct_all_region_selfattachments_are_preserved(self):
        self.assertTrue(verify_normal_geometric_descent(self.small, self.direct))
        self.assertEqual(_prepare(self.small, lambda: None)['vertices'], 1)
        certificate = self.direct['steps'][0]['certificate']
        region = {item['tetrahedron']: item['vertices'] for item in certificate['region']}
        facets = {(t, f) for t, labels in region.items() for f in range(4) if labels[f] in (3, 4)}
        attachments = set()
        boundary_count = 0
        for t, f in facets:
            entry = self.small['tetrahedra'][t][f]
            if entry is None:
                boundary_count += 1
            else:
                target = (entry['tetrahedron'], entry['permutation'][f])
                self.assertIn(target, facets)
                attachments.add(tuple(sorted(((t, f), target))))
        self.assertEqual((len(facets), len(attachments), boundary_count), (6, 2, 2))

    def test_no_discovery_cochain_cover_or_solver_dependency_and_no_mutation(self):
        saved = deepcopy((self.source, self.packet, self.small, self.direct))
        with ExitStack() as stack:
            for module, name in [('pachner23', 'pachner_23'), ('pachner32', 'pachner_32'),
                                 ('normal_geometric_descent', 'reduce_geometric_descent_once'),
                                 ('normal_pachner_descent', 'reduce_pachner_descent_once'),
                                 ('pachner_cover_search', 'find_pachner_descent'),
                                 ('pachner_cover_search', 'search_pachner_cover'),
                                 ('pachner_cover_verify', 'inspect_pachner_descent'),
                                 ('cocycle_transport', 'transport_cocycle'),
                                 ('normal_euler_transversal', 'search_euler_transversal'),
                                 ('exact_lp', 'solve_nonnegative_kernel')]:
                stack.enter_context(patch('fastunknot.'+module+'.'+name,
                                          side_effect=AssertionError('discovery or cochain replay called')))
            self.assertTrue(verify_normal_geometric_descent(self.source, self.packet))
            self.assertTrue(verify_normal_geometric_descent(self.small, self.direct))
        self.assertEqual((self.source, self.packet, self.small, self.direct), saved)

    def test_exact_outer_and_step_schema_and_literal_move_fields(self):
        for bad in (None, [], {}, dict(self.packet, extra=0), dict(self.packet, schema=True),
                    dict(self.packet, schema='normal-pachner-descent-v1'),
                    dict(self.packet, source_sha256=False), dict(self.packet, source_sha256='0'*64),
                    dict(self.packet, successor=None), dict(self.packet, steps=tuple(self.packet['steps']))):
            self.assertFalse(verify_normal_geometric_descent(self.source, bad))
        for field in self.packet:
            bad = deepcopy(self.packet)
            del bad[field]
            self.assertFalse(verify_normal_geometric_descent(self.source, bad))
        for i in range(3):
            for field, value in [('extra', 0), ('triangulation', None), ('certificate', None)]:
                bad = deepcopy(self.packet)
                bad['steps'][i][field] = value
                self.assertFalse(verify_normal_geometric_descent(self.source, bad))
            for field in ('triangulation', 'certificate'):
                bad = deepcopy(self.packet)
                del bad['steps'][i][field]
                self.assertFalse(verify_normal_geometric_descent(self.source, bad))
            for field, value in [('schema', True), ('extra', 0)]:
                bad = deepcopy(self.packet)
                bad['steps'][i]['certificate'][field] = value
                self.assertFalse(verify_normal_geometric_descent(self.source, bad))
        for value in (True, 1.0, '1', -1):
            bad = deepcopy(self.packet)
            bad['steps'][0]['certificate']['tetrahedron'] = value
            self.assertFalse(verify_normal_geometric_descent(self.source, bad))
            bad = deepcopy(self.packet)
            bad['steps'][0]['certificate']['face'] = value
            self.assertFalse(verify_normal_geometric_descent(self.source, bad))
        for index in (1, 2):
            for value in (True, 1.0, '1', -1):
                bad = deepcopy(self.packet)
                bad['steps'][index]['certificate']['region'][0]['tetrahedron'] = value
                self.assertFalse(verify_normal_geometric_descent(self.source, bad))
                bad = deepcopy(self.packet)
                bad['steps'][index]['certificate']['region'][0]['vertices'][0] = value
                self.assertFalse(verify_normal_geometric_descent(self.source, bad))

    def test_genuine_legacy_dud_and_incomplete_or_reordered_paths_are_rejected(self):
        from tests.test_normal_pachner_descent_verify import _packet as old_packet
        from fastunknot.pachner_cover_verify import inspect_pachner_descent
        operations = [('down', 0, [0, 1]), ('up', 0, 0), ('down', 0, [0, 1])]
        packet = _packet(self.small, operations)
        self.assertEqual([len(step['triangulation']['tetrahedra']) for step in packet['steps']], [2, 3, 2])
        self.assertTrue(_elementary_replay(self.small, packet))
        legacy = old_packet(self.small, operations, range(3))
        self.assertIsNotNone(inspect_pachner_descent(
            self.small, [[0]*4 for _ in self.small['tetrahedra']], legacy['certificate'], max_upward=1))
        self.assertFalse(verify_normal_geometric_descent(self.small, packet))
        for steps in ([], self.packet['steps'][:1], self.packet['steps'][:2],
                      list(reversed(self.packet['steps'])), self.packet['steps']*2):
            self.assertFalse(verify_normal_geometric_descent(self.source, dict(self.packet, steps=steps)))

    def test_source_geometry_binding_and_every_intermediate_table_are_checked(self):
        for source in (None, {}, {'tetrahedra': []}, {'tetrahedra': [[None]*4]},
                       dict(self.source, extra=0), self.small):
            self.assertFalse(verify_normal_geometric_descent(source, self.packet))
        bad_source = deepcopy(self.source)
        record = next(record for row in bad_source['tetrahedra'] for record in row if record is not None)
        record['tetrahedron'] = True
        self.assertFalse(verify_normal_geometric_descent(
            bad_source, dict(self.packet, source_sha256=_digest(bad_source))))
        # A freshly rehashed disconnected collection of balls is not supported
        # merely because its table has the same number of tetrahedra.
        bad_source = {'tetrahedra': [[None]*4 for _ in self.source['tetrahedra']]}
        self.assertFalse(verify_normal_geometric_descent(
            bad_source, dict(self.packet, source_sha256=_digest(bad_source))))
        for i in range(3):
            for mutation in ('nonreciprocal', 'tuple', 'extra', 'float'):
                bad = deepcopy(self.packet)
                after = bad['steps'][i]['triangulation']
                rows = after['tetrahedra']
                if mutation == 'nonreciprocal':
                    t, f = next((t, f) for t, row in enumerate(rows) for f, value in enumerate(row) if value is not None)
                    rows[t][f] = None
                elif mutation == 'tuple':
                    after['tetrahedra'] = tuple(rows)
                elif mutation == 'extra':
                    after['extra'] = 0
                else:
                    record = next(record for row in rows for record in row if record is not None)
                    record['permutation'][0] = float(record['permutation'][0])
                with self.subTest(step=i, mutation=mutation):
                    self.assertFalse(verify_normal_geometric_descent(self.source, bad))

    def test_outer_successor_uses_typed_equality_after_valid_inner_replay(self):
        for value in (False, 0.0):
            bad = deepcopy(self.packet)
            bad['successor'] = deepcopy(bad['successor'])
            record = next(record for row in bad['successor']['tetrahedra'] for record in row
                          if record is not None and 0 in record['permutation'])
            record['permutation'][record['permutation'].index(0)] = value
            self.assertTrue(_elementary_replay(self.source, bad))
            self.assertEqual(bad['successor'], bad['steps'][-1]['triangulation'])
            self.assertFalse(verify_normal_geometric_descent(self.source, bad))
        bad = deepcopy(self.packet)
        bad['successor'] = deepcopy(bad['successor'])
        bad['successor']['tetrahedra'] = tuple(bad['successor']['tetrahedra'])
        self.assertTrue(_elementary_replay(self.source, bad))
        self.assertFalse(verify_normal_geometric_descent(self.source, bad))

    def test_callback_identity_inside_validation_boundary_maps_and_final_comparison(self):
        calls, positions = [0], {}
        stages = {'_prepare', 'verify_pachner_23', 'verify_pachner_32', '_boundary_signature', '_same'}
        def count():
            calls[0] += 1
            frame = inspect.currentframe().f_back
            while frame:
                name = frame.f_code.co_name
                if name in stages:
                    positions.setdefault(name, calls[0])
                    break
                frame = frame.f_back
        self.assertTrue(verify_normal_geometric_descent(self.source, self.packet, check=count))
        self.assertEqual(set(positions), stages)
        stops = sorted({1, calls[0], *positions.values()})
        class CallerStop(BaseException):
            pass
        for error_type in (NormalOrbitError, ValueError, TypeError, KeyError, IndexError,
                           AttributeError, OverflowError, RecursionError, RuntimeError,
                           KeyboardInterrupt, SystemExit, CallerStop):
            for stop in stops:
                calls[0] = 0
                error = error_type('caller stopped replay')
                def cancel():
                    calls[0] += 1
                    if calls[0] == stop:
                        raise error
                with self.subTest(error=error_type, stop=stop):
                    with self.assertRaises(error_type) as raised:
                        verify_normal_geometric_descent(self.source, self.packet, check=cancel)
                    self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
