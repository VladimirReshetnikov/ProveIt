"""Exact transfer identities and the supported production API boundaries."""
from collections import Counter
from contextlib import redirect_stderr, redirect_stdout
import copy
import io
import json
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

from fastunknot import Diagram, factored_khovanov_rank, khovanov_rank, recognize
from fastunknot import __main__ as cli
from fastunknot.component_algebra import install_on_empty_scan
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.graded_transfer import (
    GradedAdaptiveScan, GradedTransferScan, check_certificate, transfer,
)
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


EXAMPLES = Path(__file__).resolve().parents[1] / 'examples'
MODES = ('graded', 'graded-adaptive', 'corridor', 'corridor-adaptive')
SCAN_OPTIONS = dict(use_braid=False, use_seifert=False, use_reduction=False,
                    use_descending=False, use_alexander=False, use_jones=False,
                    use_factorization=False)


def example(name):
    return Diagram.from_json(json.loads((EXAMPLES / (name + '.json')).read_text()))


def quantum_counts(scan):
    return Counter((scan.deg[v], scan.qshift[v])
                   for v, matching in enumerate(scan.mid) if matching is not None)


def small_complex(scan_type, degrees, quantum, rows, arcs=1):
    scan = scan_type(shape_cache=False)
    matching = scan.algebra.intern(tuple((2*j, 2*j+1) for j in range(arcs)))
    scan.points = frozenset(range(2*arcs))
    scan.mid = [matching] * len(degrees)
    scan.deg = list(degrees)
    scan.qshift = list(quantum)
    scan.out = copy.deepcopy(rows)
    scan.inc = [set() for _ in degrees]
    scan.live = len(degrees)
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    return scan


class GradedTransferIntegrationTests(unittest.TestCase):
    def test_full_nonzero_transfer_and_relative_continuation(self):
        rows = [{2: 1, 3: 2}, {2: 1}, {}, {}]
        old = small_complex(FastScan, [0,0,1,1], [0,0,0,2], rows)
        changed = small_complex(GradedTransferScan, [0,0,1,1], [0,0,0,2], rows)
        result = transfer(changed, certificates=True)
        self.assertEqual(len(check_certificate(changed, result)), 8)
        self.assertEqual(result['out'], [{1: 2}, {}])
        changed.certificates = True
        changed.eliminate()
        old.eliminate()
        old.add_crossing((0,1,2,2))
        changed.add_crossing((0,1,2,2))
        self.assertEqual(changed.ranks_by_degree(), old.ranks_by_degree())

    def test_higher_correction_and_source_quantum_band(self):
        # A two-step correction x1*x2 survives at the top possible weight.
        scan = small_complex(GradedTransferScan, [0,1,0,1], [0,2,2,4],
                             [{1:2}, {}, {1:1,3:4}, {}], arcs=2)
        result = transfer(scan, certificates=True)
        self.assertEqual(result['out'], [{1:8}, {}])
        check_certificate(scan, result)
        # On one arc the same two-step path becomes x*x=0 beyond its band.
        scan = small_complex(GradedTransferScan, [0,1,0,1], [0,2,2,4],
                             [{1:2}, {}, {1:1,3:2}, {}])
        result = transfer(scan, certificates=True)
        self.assertEqual(result['out'], [{}, {}])
        check_certificate(scan, result)

    def test_quantum_ranks_and_exact_certificates_with_composition(self):
        from audit_grading import GradingAuditScan
        for name in ('trefoil', 'hard_unknot_8', 'conway'):
            diagram = example(name)
            order = best_scan_order(diagram.pd)
            baseline = GradingAuditScan(shape_cache=False)
            changed = GradedTransferScan(shape_cache=False, certificates=True)
            install_on_empty_scan(changed, minimum_pairs=0, method='fast')
            for crossing in order:
                baseline.add_crossing(diagram.pd[crossing])
                changed.add_crossing(diagram.pd[crossing])
            self.assertEqual(quantum_counts(changed), quantum_counts(baseline))
            self.assertEqual(changed.ranks_by_degree(), baseline.ranks_by_degree())

    def test_public_ranks_tail_and_coefficient_adapters(self):
        for name in ('trefoil', 'hard_unknot_8', 'conway'):
            diagram = example(name)
            expected = khovanov_rank(diagram.pd)['by_degree']
            for mode in MODES:
                for composition in ('standard', 'component', 'component-dense'):
                    for tail in (0,2):
                        result = khovanov_rank(diagram.pd, reduction=mode,
                                               composition=composition, tail=tail,
                                               check_d_squared=True)
                        self.assertEqual(result['by_degree'], expected)
                        self.assertEqual(result['reduction'], mode)
                        self.assertIn('corridor_stages' if mode.startswith('corridor') else
                                      'graded_transfer_stages', result['stats'])

    def test_random_diagrams_against_the_set_coefficient_oracle(self):
        rng = random.Random(2026100817)
        accepted = 0
        while accepted < 18:
            strands = rng.randrange(2,5)
            word = [rng.choice((-1,1))*rng.randrange(1,strands)
                    for _ in range(rng.randrange(1,10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            expected = khovanov_rank(diagram.pd, order=order,
                                     algebra='sets', pivot='lifo')['by_degree']
            for mode in MODES:
                result = khovanov_rank(diagram.pd, order=order, reduction=mode,
                                       composition='component-dense', check_d_squared=True)
                self.assertEqual(result['by_degree'], expected, (strands, word, order))
            accepted += 1

    def test_adaptive_fallback_preserves_a_nonzero_radical_map(self):
        from benchmark_residue import dense_two_term
        scan = dense_two_term(GradedAdaptiveScan, 32, graded=True)
        scan.qshift = [0] * len(scan.mid)
        a = len(scan.mid)
        scan.mid.extend([scan.mid[0], scan.mid[0]])
        scan.deg.extend([0,1])
        scan.qshift.extend([0,2])
        scan.out.extend([{a+1:2}, {}])
        scan.inc.extend([set(), {a}])
        scan.live += 2
        scan.certificates = True
        scan.eliminate()
        self.assertEqual(scan.live, 3)
        self.assertGreater(scan.stats['schur_update_pairs'], 0)
        self.assertEqual(scan.stats['graded_transfer_stages'], 1)
        self.assertEqual([value for row in scan.out for value in row.values()], [2])
        scan.check_d_squared()

    def test_transfer_capacity_and_deadlines(self):
        for scan_type in (GradedTransferScan, GradedAdaptiveScan):
            scan = small_complex(scan_type, [0,0,1,1], [0,0,0,2],
                                 [{2:1,3:2},{2:1},{},{}])
            scan.max_transfer_objects = 0
            scan.eliminate()
            self.assertEqual(scan.live, 2)
            self.assertEqual([v for row in scan.out if row for v in row.values()], [2])
        for mode in MODES:
            with self.assertRaises(ScanLimit):
                khovanov_rank(example('trefoil').pd, reduction=mode, max_objects=1)
            with self.assertRaises(ScanLimit):
                khovanov_rank(example('trefoil').pd, reduction=mode, seconds=0)
        scan = GradedTransferScan(deadline=0)
        with self.assertRaises(ScanLimit):
            scan.eliminate()
        for options in ({'max_transfer_objects': -1}, {'transfer_minimum': -1}):
            with self.assertRaises(ValueError):
                GradedTransferScan(**options)

    def test_recognition_evidence_and_resource_verdicts(self):
        diagram = example('trefoil')
        for mode in MODES:
            result = recognize(diagram, reduction=mode, **SCAN_OPTIONS)
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.evidence['khovanov']['reduction'], mode)
            self.assertEqual(recognize(diagram, reduction=mode, max_objects=1,
                                       **SCAN_OPTIONS).status, 'UNKNOWN')
            self.assertEqual(recognize(diagram, reduction=mode, seconds=0,
                                       **SCAN_OPTIONS).status, 'UNKNOWN')

    def test_raw_option_guards_even_for_an_empty_diagram(self):
        for mode in MODES:
            for options in ({'pivot':'lifo'}, {'algebra':'sets'},
                            {'self_inverse':False}, {'race':2}):
                with self.assertRaises(ValueError):
                    khovanov_rank([], reduction=mode, **options)

    def test_incompatible_recognition_options_precede_early_certificates(self):
        diagram = Diagram.from_braid(2, [1,1,1])
        for mode in MODES:
            for options in ({'backend':'shared'}, {'backend':'saturated'},
                            {'backend':'euler'}, {'backend':'twist'},
                            {'pivot':'lifo'}, {'algebra':'sets'}, {'race':2},
                            {'window_radius':0}, {'window_radius':2}):
                with self.assertRaises(ValueError):
                    recognize(diagram, reduction=mode, **options)

    def test_factored_api_and_unchanged_defaults(self):
        diagram = example('conway_sum_2')
        expected = factored_khovanov_rank(diagram)['by_degree']
        for mode in MODES:
            self.assertEqual(factored_khovanov_rank(diagram, reduction=mode)['by_degree'], expected)
        default = khovanov_rank(example('trefoil').pd)
        self.assertNotIn('reduction', default)
        self.assertNotIn('graded_transfer_stages', default['stats'])
        for command in ('recognize','khovanov','window'):
            option = next(row for row in cli.OPTIONS[command] if row[0] == '--reduction')
            self.assertEqual(option[2], 'standard')
        window = next(row for row in cli.OPTIONS['window'] if row[0] == '--reduction')
        self.assertEqual(window[3], ('standard','residue','adaptive','disk-adaptive'))

    def test_both_cli_parsers_and_supported_commands(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'trefoil.json'
            path.write_text(json.dumps({'braid':{'strands':2,'word':[1,1,1]}}))
            for mode in MODES:
                fast_args = ['khovanov', str(path), '--reduction', mode]
                self.assertEqual(cli._fast_parse(fast_args).reduction, mode)
                output = io.StringIO()
                with patch.object(cli, '_parser', side_effect=AssertionError('fast parse declined')):
                    with redirect_stdout(output):
                        self.assertEqual(cli.main(fast_args), 0)
                self.assertEqual(json.loads(output.getvalue())['rank'], 6)
                full_args = ['khovanov', str(path), '--reduction='+mode]
                self.assertIsNone(cli._fast_parse(full_args))
                output = io.StringIO()
                with redirect_stdout(output):
                    self.assertEqual(cli.main(full_args), 0)
                self.assertEqual(json.loads(output.getvalue())['reduction'], mode)
                args = ['recognize', str(path), '--reduction', mode,
                        '--no-braid','--no-seifert','--no-reduction','--no-descending',
                        '--no-alexander','--no-jones','--no-factor']
                output = io.StringIO()
                with redirect_stdout(output):
                    self.assertEqual(cli.main(args), 0)
                self.assertEqual(json.loads(output.getvalue())['evidence']['khovanov']['reduction'], mode)

    def test_cli_rejects_unsafe_combinations(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'trefoil.json'
            path.write_text(json.dumps({'braid':{'strands':2,'word':[1,1,1]}}))
            for mode in MODES:
                for flag in ('--shared','--twist'):
                    with redirect_stderr(io.StringIO()):
                        self.assertEqual(cli.main(['khovanov',str(path),'--reduction',mode,flag]), 2)
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(cli.main(['recognize',str(path),'--reduction',mode,
                                               '--window-radius','0']), 2)
                with redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as raised:
                        cli._parser().parse_args(['window',str(path),'--reduction',mode])
                    self.assertEqual(raised.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
