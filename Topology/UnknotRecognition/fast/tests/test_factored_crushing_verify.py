"""Independent factor reconstruction and native child-proof boundary tests."""
from contextlib import ExitStack
from copy import deepcopy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.interlace import visible_factors_interlacement
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.factored_crushing_verify import (
    _factor_diagrams, verify_factored_crushing_recognition)
from tests.test_interlace import words, word_pd


class FactoredCrushingVerifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.children = {}
        cls.cases = {}
        for name, strands, braid, status in (
                ('circle', 1, [], 'UNKNOT'),
                ('curl', 2, [1], 'UNKNOT'),
                ('two_curls', 3, [1, 2], 'UNKNOT'),
                ('nested_curls', 0, None, 'UNKNOT'),
                ('two_trefoils', 3, [1, 1, 1, 2, 2, 2], 'KNOTTED'),
                ('trefoil_curl', 3, [1, 1, 1, 2], 'KNOTTED')):
            diagram = (word_pd((0, 1, 1, 2, 2, 0), 0) if braid is None
                       else Diagram.from_braid(strands, braid))
            factors, factorization = visible_factors_interlacement(diagram)
            proofs = []
            for index, child in enumerate(factors):
                if status == 'KNOTTED' and child.crossings != 3:
                    continue
                if child.pd not in cls.children:
                    result = recognize_by_crushing(child, sector_method='transversal',
                        transversal_candidate_policy='conflicts', max_tree_nodes=256,
                        max_pivots=10000, max_anchors=10000, max_hitting_subsets=10000)
                    assert result['status'] in ('UNKNOT', 'KNOTTED'), result
                    cls.children[child.pd] = result['certificate']
                packet = cls.children[child.pd]
                assert packet['status'] == status
                if status == 'UNKNOT' or not proofs:
                    proofs.append(dict(factor_index=index, certificate=packet))
            certificate = dict(schema='diagram-factor-crushing-v1', status=status,
                input_pd=[list(row) for row in diagram.pd], factorization=factorization,
                factor_pds=[[list(row) for row in child.pd] for child in factors], proofs=proofs)
            assert verify_factored_crushing_recognition(diagram, certificate)
            cls.cases[name] = diagram, certificate

    def rejected(self, name, change):
        diagram, certificate = self.cases[name]
        changed = deepcopy(certificate)
        change(changed)
        self.assertFalse(verify_factored_crushing_recognition(diagram, changed))

    def test_genuine_native_quorums_and_empty_single_conventions(self):
        for name, (diagram, certificate) in self.cases.items():
            with self.subTest(name=name):
                self.assertTrue(verify_factored_crushing_recognition(diagram, certificate))
        _, circle = self.cases['circle']
        self.assertEqual(circle['factorization']['crossing_components'], [])
        self.assertEqual(circle['factor_pds'], [[]])
        self.assertEqual(circle['proofs'][0]['factor_index'], 0)
        diagram, curl = self.cases['curl']
        self.assertEqual(curl['factor_pds'], [[list(row) for row in diagram.pd]])

    def test_independent_reconstruction_all_small_spherical_words(self):
        count = 0
        for n in range(5):
            for word in words(n):
                for mask in range(1 << n):
                    try:
                        diagram = word_pd(word, mask)
                    except DiagramError:
                        continue
                    factors, certificate = visible_factors_interlacement(diagram)
                    self.assertEqual(_factor_diagrams(diagram, certificate, lambda: None), factors)
                    count += 1
        self.assertEqual(count, 313)

    def test_missing_duplicated_reordered_and_wrong_quorum_indices(self):
        for label, change in (
                ('missing', lambda x: x['proofs'].pop()),
                ('duplicate', lambda x: x['proofs'][1].update(factor_index=0)),
                ('reordered', lambda x: x['proofs'].reverse()),
                ('extra', lambda x: x['proofs'].append(deepcopy(x['proofs'][0]))),
                ('unknown field', lambda x: x['proofs'][0].update(extra=0))):
            with self.subTest(label=label):
                self.rejected('two_curls', change)
        for index in (True, False, 0.0, '0', -1, 2):
            with self.subTest(index=index):
                self.rejected('two_curls', lambda x, index=index: x['proofs'][0].update(factor_index=index))
        self.rejected('two_trefoils', lambda x: x['proofs'].clear())
        self.rejected('two_trefoils', lambda x: x['proofs'].append(deepcopy(x['proofs'][0])))
        self.rejected('circle', lambda x: x['proofs'].clear())

    def test_any_verified_negative_factor_suffices_but_wrong_child_fails(self):
        diagram, certificate = self.cases['two_trefoils']
        shifted = deepcopy(certificate)
        shifted['proofs'][0]['factor_index'] = 1
        second = Diagram.from_pd(certificate['factor_pds'][1])
        shifted['proofs'][0]['certificate'] = self.children[second.pd]
        self.assertTrue(verify_factored_crushing_recognition(diagram, shifted))
        self.rejected('two_trefoils', lambda x: x['proofs'][0].update(factor_index=1))
        self.rejected('trefoil_curl', lambda x: x['proofs'][0].update(factor_index=1))

    def test_factorization_requires_strict_canonical_partition(self):
        for name, change in (
                ('reorder', lambda f: f['crossing_components'].reverse()),
                ('group order', lambda f: f['crossing_components'][0].reverse()),
                ('duplicate', lambda f: f['crossing_components'][1].__setitem__(0, 0)),
                ('missing group', lambda f: f['crossing_components'].pop()),
                ('empty group', lambda f: f['crossing_components'].__setitem__(0, [])),
                ('bool crossing', lambda f: f['crossing_components'][0].__setitem__(0, False)),
                ('tuple crossing group', lambda f: f['crossing_components'].__setitem__(0, tuple(f['crossing_components'][0]))),
                ('float count', lambda f: f.update(original_crossings=6.0)),
                ('wrong count', lambda f: f.update(original_crossings=3)),
                ('unknown field', lambda f: f.update(extra=True)),
                ('algorithm', lambda f: f.update(algorithm='unverified'))):
            with self.subTest(name=name):
                self.rejected('two_trefoils', lambda x, change=change: change(x['factorization']))
        self.rejected('curl', lambda x: x['factorization'].update(original_crossings=True))

    def test_forest_connectivity_and_separation_are_required(self):
        for name, change in (
                ('missing forest', lambda f: f.pop('interlacement_forest')),
                ('missing edge', lambda f: f['interlacement_forest'].pop()),
                ('duplicate edge', lambda f: f['interlacement_forest'].__setitem__(1, f['interlacement_forest'][0][:])),
                ('same endpoint', lambda f: f['interlacement_forest'].__setitem__(0, [0, 0])),
                ('between groups', lambda f: f['interlacement_forest'].__setitem__(0, [0, 3])),
                ('bool endpoint', lambda f: f['interlacement_forest'][0].__setitem__(0, False)),
                ('float endpoint', lambda f: f['interlacement_forest'][0].__setitem__(0, 0.0)),
                ('tuple edge', lambda f: f['interlacement_forest'].__setitem__(0, tuple(f['interlacement_forest'][0])))):
            with self.subTest(name=name):
                self.rejected('two_trefoils', lambda x, change=change: change(x['factorization']))
        # Six singleton components have valid empty internal forests, but the
        # trefoil crossings still interlace across the claimed components.
        self.rejected('two_trefoils', lambda x: x['factorization'].update(
            crossing_components=[[i] for i in range(6)], interlacement_forest=[]))

    def test_factor_pd_requires_exact_slots_and_labels(self):
        self.rejected('two_trefoils', lambda x: x['factor_pds'].pop())
        self.rejected('two_trefoils', lambda x: x['factor_pds'].append([]))
        self.rejected('two_trefoils', lambda x: x['factor_pds'][0][0].__setitem__(0, True))
        self.rejected('two_trefoils', lambda x: x['factor_pds'][0].__setitem__(0,
            x['factor_pds'][0][0][1:]+x['factor_pds'][0][0][:1]))
        def relabel(x):
            x['factor_pds'][0] = [[1 if e == 0 else 0 if e == 1 else e for e in row]
                                 for row in x['factor_pds'][0]]
            # A label bijection gives a valid diagram, but is not the exact
            # certified deterministic child PD.
            Diagram.from_pd(x['factor_pds'][0])
        self.rejected('two_trefoils', relabel)
        self.rejected('curl', lambda x: x['input_pd'][0].__setitem__(0, True))

    def test_partial_and_forged_statuses_never_become_verdicts(self):
        self.rejected('two_curls', lambda x: x.update(status='INCONCLUSIVE'))
        self.rejected('two_curls', lambda x: x.update(status='KNOTTED'))
        self.rejected('two_trefoils', lambda x: x.update(status='UNKNOT'))
        self.rejected('circle', lambda x: x['proofs'][0]['certificate'].update(status='KNOTTED'))
        self.rejected('circle', lambda x: x['proofs'][0].update(
            certificate=dict(status='INCONCLUSIVE', partial_chain=x['proofs'][0]['certificate']['chain'])))
        self.rejected('circle', lambda x: x.update(extra=True))
        self.rejected('circle', lambda x: x.pop('input_pd'))

    def test_replay_with_all_producer_entrypoints_disabled(self):
        blocked = (
            'fastunknot.interlace.visible_factors_interlacement',
            'fastunknot.interlace.interlacement_components',
            'fastunknot.factor.visible_factors',
            'fastunknot.factored_crushing.recognize_factored_by_crushing',
            'fastunknot.normal_crushing_search.recognize_by_crushing',
            'fastunknot.diagram_exterior.diagram_exterior',
            'fastunknot.normal_crushing.crush_normal_ray',
            'fastunknot.normal_vertex_reduction.vertex_reduction_ray',
            'fastunknot.boundary_unlayer.unlayer_boundary_once',
            'fastunknot.normal_euler_tree.search_euler_tree',
            'fastunknot.normal_euler_transversal.search_euler_transversal',
            'fastunknot.normal_euler.decide_sector_euler',
            'fastunknot.exact_lp.solve_nonnegative_kernel')
        with ExitStack() as stack:
            for name in blocked:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            for name in ('circle', 'two_curls', 'nested_curls', 'two_trefoils'):
                with self.subTest(name=name):
                    self.assertTrue(verify_factored_crushing_recognition(*self.cases[name]))

    def test_callback_exception_identity_early_factor_and_nested_child(self):
        diagram, certificate = self.cases['circle']
        calls = [0]
        def count():
            calls[0] += 1
        self.assertTrue(verify_factored_crushing_recognition(diagram, certificate, check=count))
        self.assertGreater(calls[0], 100)
        for kind in (ValueError, TypeError, KeyError, IndexError, AttributeError,
                     OverflowError, RuntimeError, KeyboardInterrupt, SystemExit):
            for stop in (1, 10, 100, calls[0]-1):
                error = kind('caller interruption')
                seen = [0]
                def cancel():
                    seen[0] += 1
                    if seen[0] == stop:
                        raise error
                with self.subTest(kind=kind.__name__, stop=stop):
                    with self.assertRaises(kind) as caught:
                        verify_factored_crushing_recognition(diagram, certificate, check=cancel)
                    self.assertIs(caught.exception, error)
        # The nontrivial graph's union/find loop is another independently
        # authored callback path, before any child proof is entered.
        error = ValueError('forest cancellation')
        def during_forest():
            frame = sys._getframe()
            while frame:
                if frame.f_code.co_name == 'root' and frame.f_code.co_filename.endswith('factored_crushing_verify.py'):
                    raise error
                frame = frame.f_back
        with self.assertRaises(ValueError) as caught:
            verify_factored_crushing_recognition(*self.cases['two_trefoils'], check=during_forest)
        self.assertIs(caught.exception, error)

    def test_invalid_source_is_revalidated_and_callback_still_propagates(self):
        _, certificate = self.cases['curl']
        for invalid in (Diagram(((False, 0, 1, 1),)), Diagram(((0, 0, 0, 0),)), object()):
            self.assertFalse(verify_factored_crushing_recognition(invalid, certificate))
        error = ValueError('before malformed source')
        def cancel():
            raise error
        with self.assertRaises(ValueError) as caught:
            verify_factored_crushing_recognition(object(), {}, check=cancel)
        self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
