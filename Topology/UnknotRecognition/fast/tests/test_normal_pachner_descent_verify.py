"""Strict zero-height first-descent macros and independent hostile replay."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_pachner_descent_verify import verify_normal_pachner_descent
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.normal_cocycle import CocycleLimit
from fastunknot.pachner_cover_verify import inspect_pachner_descent


def _digest(source):
    return sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _packet(source, operations, cover):
    """Construct specified actual moves only; no LP or descent search runs."""
    from fastunknot.pachner23 import pachner_23
    from fastunknot.pachner32 import pachner_32
    from fastunknot.cocycle_transport import transport_cocycle
    current, steps = source, []
    for kind, tetrahedron, port in operations:
        operation = pachner_23 if kind == 'up' else pachner_32
        answer = operation(current, tetrahedron, port)
        after = answer['triangulation']
        heights = [[0]*4 for _ in current['tetrahedra']]
        transport = transport_cocycle(current, heights, after, answer['certificate'])
        steps.append(dict(triangulation=after, transport=transport['certificate']))
        current = after
    proof = dict(schema='pachner-cochain-endpoint-v1', max_upward=1,
        active_initial_tetrahedra=list(cover), moves=steps,
        coordinates=[[0]*7 for _ in current['tetrahedra']], disc_certificate=None)
    return dict(schema='normal-pachner-descent-v1', source_sha256=_digest(source),
                certificate=proof, successor=current)


def zero_descent_fixture():
    from causal_research.fixtures import attach_gadgets
    source = attach_gadgets()['triangulation']
    # Flip through BCD, then collapse the old BC and CD edges. The solid-torus
    # source has five global vertices, and all six gadget cells are consumed.
    packet = _packet(source, [('up', 1, 0), ('down', 1, [1, 2]), ('down', 1, [1, 2])], range(1, 7))
    return source, packet


class NormalPachnerDescentVerifyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source, cls.packet = zero_descent_fixture()

    def test_genuine_three_move_multivertex_macro_and_single_downward_macro(self):
        source, packet = self.source, self.packet
        self.assertEqual(_prepare(source, lambda: None)['vertices'], 5)
        self.assertEqual([len(step['triangulation']['tetrahedra'])
                          for step in packet['certificate']['moves']], [8, 7, 6])
        self.assertTrue(verify_normal_pachner_descent(source, packet))
        from tests.test_normal_pachner32_verify import selfattached_fixture
        small, _ = selfattached_fixture()
        direct = _packet(small, [('down', 0, [0, 1])], range(3))
        self.assertTrue(verify_normal_pachner_descent(small, direct))

    def test_independent_replay_imports_no_producer_and_preserves_input(self):
        saved = deepcopy((self.source, self.packet))
        with ExitStack() as stack:
            for module, name in [('pachner23', 'pachner_23'), ('pachner32', 'pachner_32'),
                                 ('pachner_cover_search', 'find_pachner_descent'),
                                 ('pachner_cover_search', 'search_pachner_cover'),
                                 ('normal_pachner_descent', 'reduce_pachner_descent_once'),
                                 ('cocycle_transport', 'transport_cocycle'),
                                 ('normal_cocycle', 'local_coordinates'),
                                 ('normal_euler_transversal', 'search_euler_transversal'),
                                 ('exact_lp', 'solve_nonnegative_kernel')]:
                stack.enter_context(patch('fastunknot.'+module+'.'+name,
                                          side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_pachner_descent(self.source, self.packet))
        self.assertEqual((self.source, self.packet), saved)

    def test_strict_source_bound_outer_and_legacy_schemas(self):
        source, packet = self.source, self.packet
        for bad in (None, {}, [], dict(packet, extra=0), dict(packet, schema=True),
                    dict(packet, source_sha256=False), dict(packet, source_sha256='0'*64),
                    dict(packet, successor=None), dict(packet, certificate=None)):
            self.assertFalse(verify_normal_pachner_descent(source, bad))
        for field in packet:
            bad = deepcopy(packet)
            del bad[field]
            self.assertFalse(verify_normal_pachner_descent(source, bad))
        for field, value in [('schema', True), ('max_upward', True), ('max_upward', 1.0),
                             ('max_upward', 0), ('max_upward', 2), ('disc_certificate', {}),
                             ('moves', []), ('moves', tuple(packet['certificate']['moves'])),
                             ('moves', packet['certificate']['moves']*2),
                             ('active_initial_tetrahedra', [True, 2, 3, 4, 5, 6]),
                             ('active_initial_tetrahedra', list(range(7))), ('extra', 0)]:
            bad = deepcopy(packet)
            bad['certificate'][field] = value
            with self.subTest(field=field, value=value):
                self.assertFalse(verify_normal_pachner_descent(source, bad))
        for bad in (None, {}, {'tetrahedra': []}, dict(source, extra=0)):
            self.assertFalse(verify_normal_pachner_descent(bad, packet))

    def test_every_intermediate_zero_field_has_literal_integer_types(self):
        for index in range(3):
            for field, width in [('heights', 4), ('coordinates', 7), ('bipyramid_heights', 5)]:
                for value in (1, False, 0.0, '0x0'):
                    bad = deepcopy(self.packet)
                    array = bad['certificate']['moves'][index]['transport'][field]
                    if field == 'bipyramid_heights':
                        array[0] = value
                    else:
                        array[0][0] = value
                    with self.subTest(step=index, field=field, value=value):
                        self.assertFalse(verify_normal_pachner_descent(self.source, bad))
                bad = deepcopy(self.packet)
                bad['certificate']['moves'][index]['transport'][field] = [0]*(width-1)
                self.assertFalse(verify_normal_pachner_descent(self.source, bad))
            for field in ('euler_jump', 'normal_disc_jump'):
                for value in (1, False, 0.0, '0x0'):
                    bad = deepcopy(self.packet)
                    bad['certificate']['moves'][index]['transport'][field] = value
                    self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        for value in (1, False, 0.0, '0x0'):
            bad = deepcopy(self.packet)
            bad['certificate']['coordinates'][0][0] = value
            self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        # Legacy integer transport permits hexadecimal zero; the new packet's
        # deliberately narrower literal-zero policy rejects that representation.
        bad = deepcopy(self.packet)
        bad['certificate']['moves'][0]['transport']['heights'][0][0] = '0x0'
        self.assertIsNotNone(inspect_pachner_descent(self.source, [[0]*4 for _ in self.source['tetrahedra']],
                                                   bad['certificate'], max_upward=1))
        self.assertFalse(verify_normal_pachner_descent(self.source, bad))

    def test_legacy_valid_endpoint_with_an_earlier_descent_is_rejected(self):
        from tests.test_normal_pachner32_verify import selfattached_fixture
        source, _ = selfattached_fixture()
        packet = _packet(source, [('down', 0, [0, 1]), ('up', 0, 0), ('down', 0, [0, 1])], range(3))
        self.assertEqual([len(s['triangulation']['tetrahedra']) for s in packet['certificate']['moves']], [2, 3, 2])
        self.assertIsNotNone(inspect_pachner_descent(source, [[0]*4 for _ in source['tetrahedra']],
                                                   packet['certificate'], max_upward=1))
        self.assertFalse(verify_normal_pachner_descent(source, packet))

    def test_exact_successor_and_all_source_move_maps_are_checked(self):
        for value in (False, 0.0):
            bad = deepcopy(self.packet)
            # Break the producer's benign last-step/successor alias so only
            # the outer declaration changes, exercising literal equality.
            bad['successor'] = deepcopy(bad['successor'])
            record = next(record for row in bad['successor']['tetrahedra'] for record in row
                          if record is not None and 0 in record['permutation'])
            record['permutation'][record['permutation'].index(0)] = value
            self.assertIsNotNone(inspect_pachner_descent(
                self.source, [[0]*4 for _ in self.source['tetrahedra']],
                bad['certificate'], max_upward=1))
            self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        bad = deepcopy(self.packet)
        bad['successor'] = deepcopy(bad['successor'])
        bad['successor']['tetrahedra'] = tuple(bad['successor']['tetrahedra'])
        self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        for index in range(3):
            bad = deepcopy(self.packet)
            rows = bad['certificate']['moves'][index]['triangulation']['tetrahedra']
            t, f = next((t, f) for t, row in enumerate(rows) for f, entry in enumerate(row) if entry is not None)
            rows[t][f] = None
            self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        bad = deepcopy(self.packet)
        bad['certificate']['moves'].reverse()
        self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        bad = deepcopy(self.packet)
        bad['certificate']['moves'][0]['transport']['move']['tetrahedron'] = True
        self.assertFalse(verify_normal_pachner_descent(self.source, bad))
        bad_source = deepcopy(self.source)
        bad_source['tetrahedra'][0][0]['tetrahedron'] = True
        bad = dict(self.packet, source_sha256=_digest(bad_source))
        self.assertFalse(verify_normal_pachner_descent(bad_source, bad))

    def test_callback_exception_identity_through_every_replay_layer(self):
        calls = [0]
        positions = {}
        import inspect
        def count():
            calls[0] += 1
            # Identify representative callbacks inside each independently
            # nested stage without assuming their present checkpoint counts.
            frame = inspect.currentframe().f_back
            while frame:
                name = frame.f_code.co_name
                if name in ('_prepare', 'verify_cocycle_transport', 'inspect_pachner_cover', '_same'):
                    positions.setdefault(name, calls[0])
                    break
                frame = frame.f_back
        self.assertTrue(verify_normal_pachner_descent(self.source, self.packet, check=count))
        self.assertEqual(set(positions), {'_prepare', 'verify_cocycle_transport', 'inspect_pachner_cover', '_same'})
        stops = sorted({1, calls[0], *positions.values()})
        class CallerStop(BaseException):
            pass
        for error_type in (NormalOrbitError, CocycleLimit, ValueError, TypeError,
                           KeyError, IndexError, AttributeError, OverflowError,
                           RuntimeError, KeyboardInterrupt, SystemExit, CallerStop):
            for stop in stops:
                calls[0] = 0
                error = error_type('caller interrupted a nested replay')
                def cancel():
                    calls[0] += 1
                    if calls[0] == stop:
                        raise error
                with self.subTest(error=error_type, stop=stop):
                    with self.assertRaises(error_type) as raised:
                        verify_normal_pachner_descent(self.source, self.packet, check=cancel)
                    self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
