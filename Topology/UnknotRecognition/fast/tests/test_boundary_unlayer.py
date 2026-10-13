"""Exact collar deletion, hostile proof replay, and shared reduction limits."""
from contextlib import ExitStack
from copy import deepcopy
from random import Random
import unittest
from unittest.mock import patch

from fastunknot.boundary_unlayer import unlayer_boundary_once
from fastunknot.boundary_unlayer_verify import verify_boundary_unlayering
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from normal_orbit_research.fixtures import layered_torus
from boundary_transversal_research.common import load


def relabel(source, order, vertices):
    index = {old: new for new, old in enumerate(order)}
    rows = []
    for old in order:
        row = [None]*4
        for face, record in enumerate(source['tetrahedra'][old]):
            if record is not None:
                other = record['tetrahedron']
                permutation = [None]*4
                for vertex in range(4):
                    permutation[vertices[old][vertex]] = vertices[other][record['permutation'][vertex]]
                row[vertices[old][face]] = dict(tetrahedron=index[other], permutation=permutation)
        rows.append(row)
    return dict(tetrahedra=rows)


class BoundaryUnlayerTests(unittest.TestCase):
    def test_six_retained_inverse_layers_recover_exact_sources(self):
        for record in load('provenance/layer-refuter.json')['records']:
            expected = [record['initial_source']]+[s['source'] for s in record['steps']]
            current = expected[-1]
            for before in reversed(expected[:-1]):
                result = unlayer_boundary_once(current)
                self.assertEqual(result['status'], 'UNLAYERED')
                self.assertTrue(verify_boundary_unlayering(current, result['certificate']))
                self.assertEqual(result['certificate']['successor'], before)
                self.assertEqual(result['stats']['moves'], 1)
                current = before
            self.assertEqual(unlayer_boundary_once(current)['status'], 'UNCHANGED')

    def test_dense_deletion_respects_arbitrary_tetrahedron_and_vertex_labels(self):
        rng = Random(2026101303)
        small, large = layered_torus(4)[0], layered_torus(5)[0]
        for _ in range(16):
            order = list(range(5))
            rng.shuffle(order)
            vertices = [rng.sample(range(4), 4) for _ in order]
            source = relabel(large, order, vertices)
            result = unlayer_boundary_once(source)
            self.assertEqual(result['status'], 'UNLAYERED')
            self.assertEqual(result['certificate']['tetrahedron'], order.index(0))
            # The reference smaller fixture omits old tetrahedron zero.
            expected = relabel(small, [t-1 for t in order if t], vertices[1:])
            self.assertEqual(result['certificate']['successor'], expected)
            self.assertTrue(verify_boundary_unlayering(source, result['certificate']))

    def test_long_collar_strictly_descends_and_stops_at_nonempty_core(self):
        source = layered_torus(32)[0]
        for remaining in range(31, 0, -1):
            result = unlayer_boundary_once(source)
            self.assertEqual(result['status'], 'UNLAYERED')
            source = result['certificate']['successor']
            self.assertEqual(source, layered_torus(remaining)[0])
        result = unlayer_boundary_once(source)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertNotIn('certificate', result)

    def test_replay_rejects_foreign_source_malformed_packet_and_bad_successor(self):
        source = layered_torus(3)[0]
        packet = unlayer_boundary_once(source)['certificate']
        changes = [dict(extra=0), dict(schema='unknown'), dict(tetrahedron=True),
                   dict(tetrahedron=-1), dict(tetrahedron=1), dict(source_sha256='0'*64),
                   dict(successor=source), dict(successor=None), dict(successor={'tetrahedra': []})]
        for change in changes:
            changed = deepcopy(packet)
            changed.update(change)
            self.assertFalse(verify_boundary_unlayering(source, changed), change)
        self.assertFalse(verify_boundary_unlayering(layered_torus(4)[0], packet))
        changed = deepcopy(packet)
        changed['successor']['tetrahedra'][0][0]['permutation'][0] = True
        self.assertFalse(verify_boundary_unlayering(source, changed))

    def test_nested_callback_identity_for_producer_and_verifier(self):
        source = layered_torus(3)[0]
        packet = unlayer_boundary_once(source)['certificate']
        class CallerStop(BaseException):
            pass
        for operation in (lambda check: unlayer_boundary_once(source, check=check),
                          lambda check: verify_boundary_unlayering(source, packet, check=check)):
            calls = [0]
            def count():
                calls[0] += 1
            operation(count)
            for position in (1, 20, calls[0]//2, calls[0]):
                for kind in (ValueError, RuntimeError, CallerStop):
                    marker, seen = kind('unlayer interruption'), [0]
                    def stop():
                        seen[0] += 1
                        if seen[0] == position:
                            raise marker
                    with self.assertRaises(kind) as caught:
                        operation(stop)
                    self.assertIs(caught.exception, marker)

    def test_genuine_diagram_proofs_and_strict_option(self):
        circle = Diagram.from_pd([])
        for diagram in (circle, Diagram.from_braid(2, [1, 1, 1])):
            old = recognize_by_crushing(diagram, sector_method='transversal',
                transversal_candidate_policy='conflicts')
            new = recognize_by_crushing(diagram, sector_method='transversal',
                transversal_candidate_policy='conflicts', unlayer_boundary=True)
            self.assertEqual(old['status'], new['status'])
            self.assertEqual(new['stats']['boundary_unlayerings'], 0)
            self.assertTrue(verify_crushing_recognition(diagram, new['certificate']))
            self.assertEqual(new['certificate']['chain']['schema'], 'diagram-crushing-v2')
            with patch('fastunknot.boundary_unlayer.unlayer_boundary_once',
                       side_effect=AssertionError('discovery during independent replay')):
                self.assertTrue(verify_crushing_recognition(diagram, new['certificate']))
        for bad in (None, 0, 1, 'yes', [], {}):
            with self.assertRaises(ValueError):
                recognize_by_crushing(circle, unlayer_boundary=bad)

    def source_harness(self, source):
        # Only the external diagram-to-source premise is stubbed. The supplied
        # solid torus is independently known, but this is a scheduling test,
        # not a genuine native diagram authentication or recognition claim.
        stack = ExitStack()
        stack.enter_context(patch('fastunknot.diagram_exterior.diagram_exterior', return_value=source))
        stack.enter_context(patch('fastunknot.diagram_exterior_verify.verify_diagram_exterior', return_value=True))
        stack.enter_context(patch('fastunknot.normal_crushing_chain.verify_diagram_exterior', return_value=True))
        return stack

    def test_source_harness_shares_cap_across_real_unlayers_and_terminal_crush(self):
        circle, source = Diagram.from_pd([]), layered_torus(3)[0]
        with self.source_harness(source):
            for cap in range(4):
                result = recognize_by_crushing(circle, unlayer_boundary=True,
                    sector_method='transversal', max_crushes=cap)
                chain = (result['certificate']['chain'] if result['status'] == 'UNKNOT'
                         else result['partial_chain'])
                self.assertEqual(len(chain['steps']), cap)
                self.assertEqual(result['stats']['boundary_unlayerings'], min(2, cap))
                self.assertEqual(result['stats']['crushing_steps'], int(cap == 3))
                self.assertTrue(verify_crushing_chain(circle, chain))
                self.assertEqual(result['status'], 'UNKNOT' if cap == 3 else 'INCONCLUSIVE')
                if cap:
                    legacy = dict(chain, schema='diagram-crushing-v1')
                    self.assertFalse(verify_crushing_chain(circle, legacy))
        self.assertFalse(verify_crushing_chain(circle, chain))

    def test_driver_replays_unlayer_before_accepting_partial_progress(self):
        source = layered_torus(3)[0]
        corrupted = unlayer_boundary_once(source)
        corrupted['certificate']['successor'] = source
        with self.source_harness(source), patch(
                'fastunknot.boundary_unlayer.unlayer_boundary_once', return_value=corrupted):
            with self.assertRaisesRegex(ArithmeticError, 'independent boundary unlayering replay failed'):
                recognize_by_crushing(Diagram.from_pd([]), unlayer_boundary=True, max_crushes=1)


if __name__ == '__main__':
    unittest.main()
