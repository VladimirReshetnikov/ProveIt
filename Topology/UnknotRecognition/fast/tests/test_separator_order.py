"""Independent hierarchy, rotation, scalar-value and scan-order checks."""
import contextlib
import copy
import io
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.__main__ import main
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, order_profile
from fastunknot.potts_exact import potts_exact
from fastunknot.separator_order import (separator_scan_order, verify_separator_order,
                                       width_bounded_scan_order, verify_width_bounded_order)
from fastunknot.separator_potts import separator_potts_exact
from separator_research.graphs import tree_medial
from disk_grid import descending_grid
from disk_oracles import cube_ranks
from test_shadow_scan import diagrams, ReferenceDiagram


class SeparatorOrderTests(unittest.TestCase):
    def test_random_ribbon_maps_against_independent_sphericity(self):
        rng = random.Random(2616)
        accepted = rejected = 0
        for _ in range(500):
            n = rng.randrange(1, 7)
            darts = list(range(4*n))
            rng.shuffle(darts)
            labels = [None]*(4*n)
            for label in range(2*n):
                labels[darts[2*label]] = labels[darts[2*label+1]] = label
            pd = [tuple(labels[4*i:4*i+4]) for i in range(n)]
            try:
                ReferenceDiagram(tuple(pd))
            except ValueError:
                with self.assertRaises(ValueError):
                    separator_scan_order(pd, leaf_size=1)
                rejected += 1
            else:
                certificate = separator_scan_order(pd, leaf_size=1)
                self.assertTrue(verify_separator_order(pd, certificate))
                accepted += 1
        self.assertGreater(accepted, 100)
        self.assertGreater(rejected, 100)

    def test_grids_long_bands_loops_and_disconnected_projections(self):
        inputs = [descending_grid(m) for m in (1, 3, 8, 16, 32)]
        inputs += [Diagram.from_braid(2, [1]*257).pd, [], [(0, 0, 1, 1), (2, 2, 3, 3)]]
        for pd in inputs:
            certificate = separator_scan_order(pd, leaf_size=2)
            self.assertTrue(verify_separator_order(pd, json.loads(json.dumps(certificate))))
            self.assertLessEqual(certificate['profile'][0], certificate['width_bound'])
        d = tree_medial(7)
        bounded = width_bounded_scan_order(d.pd)
        self.assertEqual(bounded['selected'], 'separator')
        self.assertLess(bounded['profile'][0], order_profile(d.pd, best_scan_order(d.pd, tries=12))[0])
        self.assertTrue(verify_width_bounded_order(d.pd, bounded))

    def test_verifier_is_independent_and_rejects_corrupted_certificates(self):
        pd = descending_grid(4)
        certificate = separator_scan_order(pd, leaf_size=2)
        with (patch('fastunknot.separator_order._separator', side_effect=AssertionError('constructor used')),
              patch('fastunknot.separator_order._embedding', side_effect=AssertionError('embedding used'))):
            self.assertTrue(verify_separator_order(pd, certificate))
        for field, value in [('order', certificate['order'][:-1]), ('pd_sha256', 'wrong'),
                             ('width_bound', 0), ('profile', [0, 0]), ('leaf_size', True),
                             ('forest', [{'leaf': list(range(len(pd)))}])]:
            bad = copy.deepcopy(certificate)
            bad[field] = value
            self.assertFalse(verify_separator_order(pd, bad), field)
        bad = copy.deepcopy(certificate)
        bad['forest'][0]['separator'].append(bad['forest'][0]['separator'][0])
        self.assertFalse(verify_separator_order(pd, bad))
        bounded = width_bounded_scan_order(pd)
        bounded['order'] = list(reversed(bounded['order']))
        bounded['profile'] = [999, 999]
        self.assertFalse(verify_width_bounded_order(pd, bounded))

    def test_actual_separator_scans_against_independent_cube_homology(self):
        for diagram, _ in diagrams(16, 2617):
            expected = cube_ranks(diagram.pd)
            certificate = separator_scan_order(diagram.pd, leaf_size=1)
            actual = khovanov_rank(diagram.pd, order=certificate['order'], check_d_squared=True)
            self.assertEqual(actual['by_degree'], expected)
            self.assertEqual(actual['rank'], sum(expected.values()))
            for shade in (0, 1):
                a = potts_exact(diagram, shade=shade, order=list(range(diagram.crossings)))
                b = separator_potts_exact(diagram, shade=shade)
                for key in ('partition_function', 'unknot_partition', 'differs'):
                    self.assertEqual(a[key], b[key])
                self.assertLessEqual(2*b['max_spin_frontier'], b['max_boundary'])

    def test_budget_decline_retains_only_a_complete_order(self):
        d = Diagram.from_braid(3, [1, 2]*5)
        statistics = {}
        with self.assertRaises(FilterLimit):
            separator_potts_exact(d, max_transitions=1, statistics=statistics)
        self.assertEqual(set(statistics), {'order_certificate'})
        self.assertTrue(verify_width_bounded_order(d.pd, statistics['order_certificate']))
        for value in (-1, True, 1.5, 65):
            with self.assertRaises(ValueError):
                separator_scan_order(d.pd, leaf_size=value)
        statistics = {}
        calls = 0
        def stop():
            nonlocal calls
            calls += 1
            if calls == 25:
                raise ScanLimit('injected during separator preparation')
        with self.assertRaises(ScanLimit):
            separator_potts_exact(d, statistics=statistics, check=stop)
        self.assertEqual(statistics, {})
        with patch('fastunknot.separator_potts.width_bounded_scan_order', side_effect=AssertionError('zero budget prepared')):
            with self.assertRaises(FilterLimit):
                separator_potts_exact(d, max_states=0)

    def test_pipeline_reuses_the_certificate_after_scalar_decline_and_cli_routes(self):
        root = Path(__file__).resolve().parents[1] / 'examples'
        d = Diagram.from_json(json.loads((root/'hard_unknot_8.json').read_text()))
        out = recognize(d, jones_backend='potts-separator', jones_max_transitions=1,
                        use_braid=False, use_seifert=False, use_reduction=False,
                        use_descending=False, use_factorization=False, use_modular=False,
                        use_alexander=False, use_r3=False)
        self.assertEqual(out.status, 'UNKNOT')
        cert = out.evidence['separator_order']
        self.assertTrue(verify_width_bounded_order(d.pd, cert))
        self.assertEqual(out.evidence['khovanov']['scan_order'], cert['order'])
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            code = main(['jones', str(root/'trefoil.json'), '--backend', 'potts-separator'])
        self.assertEqual(code, 0)
        result = json.loads(stream.getvalue())
        self.assertEqual(result['verdict'], 'KNOTTED')
        trefoil = Diagram.from_json(json.loads((root/'trefoil.json').read_text()))
        self.assertTrue(verify_width_bounded_order(trefoil.pd, result['witness']['order_certificate']))


if __name__ == '__main__':
    unittest.main()
