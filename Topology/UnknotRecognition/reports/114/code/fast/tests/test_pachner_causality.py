"""Geometric regression checks for causal extraction, including late mergers."""
import copy
import json
from pathlib import Path
import unittest

from causal_research.fixtures import descent_gadgets
from commitment_research.fixtures import independent_bipyramids
from fastunknot.pachner_commitments import (
    _State, _Names, _events, _advance, _certificate,
)
from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint
from fastunknot.pachner_causality import (
    analyze_pachner_causality, extract_local_descent,
)
from fastunknot.pachner_cover_search import find_pachner_descent


def merged_descent():
    """Two independent downward roots subsequently merged by an upward move."""
    fixture = independent_bipyramids(2)
    raw, h = fixture['triangulation'], fixture['heights']
    n = len(raw['tetrahedra'])
    state = _State(raw, h, tuple(range(n)), 0, 0, ())
    names = _Names(n)
    groups = []
    for region in fixture['regions']:
        event = next(e for e in _events(state, True, lambda: None)
                     if e.kind == 'down' and e.cells == frozenset(region))
        before = set(state.cells)
        state = _advance(state, event, names, lambda: None)
        groups.append(set(state.cells) - before)
    bridge = next(e for e in _events(state, True, lambda: None)
                  if e.kind == 'up' and all(e.cells & group for group in groups))
    state = _advance(state, bridge, names, lambda: None)
    return fixture, _certificate(state, 1, range(n))


class CausalExtractionTests(unittest.TestCase):
    def test_noncanonical_verified_belt_frames_are_retained(self):
        path = Path(__file__).parent / 'fixtures' / 'causal_noncanonical.json'
        fixture = json.loads(path.read_text())
        raw, h, proof = (fixture[k] for k in
                         ('triangulation', 'heights', 'certificate'))
        self.assertIsNotNone(inspect_pachner_endpoint(raw, h, proof))
        extracted = extract_local_descent(raw, h, proof)
        self.assertEqual(extracted['selected_events'], [0, 1, 2])
        self.assertIsNotNone(inspect_pachner_endpoint(
            raw, h, extracted['certificate']))
        self.assertEqual(extracted['certificate']['moves'][-1]['triangulation'],
                         proof['moves'][-1]['triangulation'])

    def test_sharp_gadget_extracts_six_original_cells(self):
        fixture = descent_gadgets(1)
        raw, h = fixture['triangulation'], fixture['heights']
        result = find_pachner_descent(raw, h, max_upward=1, max_nodes=None)
        self.assertEqual(result['status'], 'DESCENT_FOUND')
        extracted = extract_local_descent(raw, h, result['certificate'])
        summary = extracted['summary']
        self.assertEqual(summary['birth_consumptions'], 2)
        self.assertEqual(summary['upward_moves'], 1)
        self.assertEqual(summary['downward_moves'], 2)
        self.assertEqual(summary['consumed_initial_tetrahedra'], list(range(1, 7)))
        self.assertTrue(summary['connected_initial_footprint'])

    def test_late_merger_then_prefix_extraction(self):
        fixture, certificate = merged_descent()
        raw, h = fixture['triangulation'], fixture['heights']
        analysis = analyze_pachner_causality(raw, h, certificate)
        self.assertEqual(analysis['event_count'], 3)
        self.assertEqual(len(analysis['components']), 1)
        self.assertEqual(analysis['dependency_edges'], [[0, 2], [1, 2]])
        extracted = extract_local_descent(raw, h, certificate)
        self.assertEqual(extracted['selected_events'], [0])
        self.assertEqual(extracted['summary']['upward_moves'], 0)
        self.assertEqual(len(extracted['certificate']['moves']), 1)
        self.assertIsNotNone(inspect_pachner_endpoint(
            raw, h, extracted['certificate']))

    def test_disconnected_descending_components(self):
        fixture = independent_bipyramids(3)
        raw, h = fixture['triangulation'], fixture['heights']
        n = len(raw['tetrahedra'])
        state = _State(raw, h, tuple(range(n)), 0, 0, ())
        names = _Names(n)
        for region in fixture['regions']:
            event = next(e for e in _events(state, False, lambda: None)
                         if e.cells == frozenset(region))
            state = _advance(state, event, names, lambda: None)
        certificate = _certificate(state, 0, range(n))
        analysis = analyze_pachner_causality(raw, h, certificate)
        self.assertEqual(len(analysis['components']), 3)
        self.assertTrue(all(c['loss'] == 1 for c in analysis['components']))
        extracted = extract_local_descent(raw, h, certificate)
        self.assertEqual(extracted['original_events'], 3)
        self.assertEqual(len(extracted['selected_events']), 1)

    def test_invalid_input_never_yields_a_trace(self):
        fixture, certificate = merged_descent()
        raw, h = fixture['triangulation'], fixture['heights']
        bad = copy.deepcopy(certificate)
        bad['moves'][0]['transport']['heights'][0][0] += 1
        self.assertIsNone(analyze_pachner_causality(raw, h, bad))
        with self.assertRaises(ValueError):
            extract_local_descent(raw, h, bad)

    def test_no_descent_is_rejected(self):
        fixture = descent_gadgets(1)
        raw, h = fixture['triangulation'], fixture['heights']
        n = len(raw['tetrahedra'])
        state = _State(raw, h, tuple(range(n)), 0, 0, ())
        certificate = _certificate(state, 0, range(n))
        self.assertEqual(analyze_pachner_causality(raw, h, certificate)['components'], [])
        with self.assertRaises(ValueError):
            extract_local_descent(raw, h, certificate)

    def test_callback_exception_identity(self):
        fixture, certificate = merged_descent()
        marker = RuntimeError('caller cancellation')
        def stop():
            raise marker
        with self.assertRaises(RuntimeError) as found:
            extract_local_descent(fixture['triangulation'], fixture['heights'],
                                  certificate, check=stop)
        self.assertIs(found.exception, marker)


if __name__ == '__main__':
    unittest.main()
