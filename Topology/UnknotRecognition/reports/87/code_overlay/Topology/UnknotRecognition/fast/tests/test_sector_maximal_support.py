"""Exact maximal support: algebraic obstructions and actual normal sources."""

from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import build_sector_kernel, sector_rays, discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion, verify_sector_witness
from fastunknot.sector_matching_support import _combined_closure, matching_support
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.sector_maximal_support import (
    certify_nonnegative_kernel_support, certify_maximal_support,
    discover_in_maximal_support_sector,
)
from fastunknot.sector_maximal_support_verify import (
    verify_nonnegative_kernel_support_certificate, verify_maximal_support_certificate,
)
from fastunknot.sector_sparse import PreparedSectorSource


BANK = Path(__file__).resolve().parents[2]/'reports/57/results/discovery_corpus.json'


def cycle_obstruction(m, effective=1):
    """An abstract rational cone, not asserted to be a triangulation sector."""
    return [[int(i == j) for j in range(m)]
            + [int(i == j)-int((i+1) % m == j) for j in range(m)]
            + [0]*(effective-1) for i in range(m)]


def solid_torus():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]}, None, None]]}


def capped_torus():
    raw = solid_torus()
    raw['tetrahedra'][0][2] = {'tetrahedron': 1, 'permutation': [0, 1, 3, 2]}
    raw['tetrahedra'].append([None, None, None,
        {'tetrahedron': 0, 'permutation': [0, 1, 3, 2]}])
    return raw


def bank_fixture():
    raw = next(row['triangulation'] for row in json.loads(BANK.read_text())['records']
               if row['id'] == 'cap_3_5_2')
    return raw, [(0, 0), (1, 1), (2, 2), (3, 0), (4, 1)]


class Cancel:
    def __init__(self, after=1):
        self.remaining = after

    def __bool__(self):
        return False

    def __call__(self):
        self.remaining -= 1
        if self.remaining <= 0:
            raise InterruptedError('maximal-support cancellation')


class RationalSupportTests(unittest.TestCase):
    def test_unbounded_row_span_obstruction_and_effective_dimension(self):
        for m, effective in ((3, 1), (4, 3), (8, 2)):
            a = cycle_obstruction(m, effective)
            forced, steps = _combined_closure(a, lambda: None)
            self.assertEqual((forced, steps), (set(), []))
            result = certify_nonnegative_kernel_support(a)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['retained_indices'], list(range(m, 2*m+effective-1)))
            self.assertEqual(result['stats']['raw_dimension'], m+effective-1)
            self.assertEqual(result['stats']['effective_dimension'], effective)
            self.assertTrue(verify_nonnegative_kernel_support_certificate(a, result['certificate']))

    def test_exact_solver_fallback_is_actually_exercised(self):
        a = cycle_obstruction(3)
        with patch('fastunknot.sector_maximal_support._scipy_solve', return_value=None):
            result = certify_nonnegative_kernel_support(a)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['stats']['solver'], 'sympy')
        self.assertEqual(result['stats']['numerical_reconstructions'], 0)
        self.assertFalse(result['stats']['polynomial_solver_guarantee'])

    def test_false_numerical_proposal_cannot_remove_a_coordinate(self):
        a = cycle_obstruction(3)
        with patch('fastunknot.sector_maximal_support._scipy_solve', return_value=[0.0]*12):
            failed = certify_nonnegative_kernel_support(a, solver='scipy')
            recovered = certify_nonnegative_kernel_support(a, solver='auto')
        self.assertEqual(failed['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', failed)
        self.assertEqual(recovered['status'], 'COMPLETE')
        self.assertEqual(recovered['stats']['solver'], 'sympy')

    def test_zero_empty_positive_degenerate_and_big_rational_inputs(self):
        cases = [([], 0, []), ([], 4, [0, 1, 2, 3]), ([[1, 0], [0, 1]], 2, []),
                 ([[1, -1], [2, -2], [0, 0]], 2, [0, 1]),
                 ([[1, 1, 0]], 3, [2]),
                 ([[Fraction(1, 2**6000+1), -1, 0]], 3, [0, 1, 2])]
        for matrix, width, retained in cases:
            with self.subTest(width=width, retained=retained):
                result = certify_nonnegative_kernel_support(matrix, width=width, solver='sympy')
                self.assertEqual(result['status'], 'COMPLETE')
                self.assertEqual(result['retained_indices'], retained)
                encoded = json.loads(json.dumps(result['certificate']))
                self.assertTrue(verify_nonnegative_kernel_support_certificate(matrix, encoded,
                                                                              width=width))

    def test_row_and_column_reordering_preserve_the_support_with_new_provenance(self):
        matrix = cycle_obstruction(4, 2)
        first = certify_nonnegative_kernel_support(matrix)['certificate']
        row_order = [2, 0, 3, 1]
        column_order = [8, 4, 0, 5, 1, 6, 2, 7, 3]
        changed = [[matrix[i][j] for j in column_order] for i in row_order]
        second = certify_nonnegative_kernel_support(changed)['certificate']
        expected = [j for j, original in enumerate(column_order) if original >= 4]
        self.assertEqual(second['retained_indices'], expected)
        self.assertTrue(verify_nonnegative_kernel_support_certificate(changed, second))
        self.assertFalse(verify_nonnegative_kernel_support_certificate(changed, first))

    def test_matrix_checker_is_independent_and_rejects_mutations(self):
        matrix = cycle_obstruction(3)
        proof = certify_nonnegative_kernel_support(matrix)['certificate']
        mutations = []
        for field in ('primal', 'dual', 'multipliers'):
            bad = deepcopy(proof); bad[field][0][0] += 1; mutations.append(bad)
            bad = deepcopy(proof); bad[field][0][1] = 0; mutations.append(bad)
            bad = deepcopy(proof); bad[field][0][0] = True; mutations.append(bad)
            bad = deepcopy(proof); bad[field].pop(); mutations.append(bad)
        bad = deepcopy(proof); bad['retained_indices'].append(0); mutations.append(bad)
        bad = deepcopy(proof); bad['input_sha256'] = '0'*64; mutations.append(bad)
        bad = deepcopy(proof); bad['primal'][3] = [1, 2]; mutations.append(bad)
        disabled = ('fastunknot.sector_maximal_support._partition',
                    'fastunknot.normal_sector._rref', 'fastunknot.normal_sector._nullspace')
        with ExitStack() as stack:
            for name in disabled:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_nonnegative_kernel_support_certificate(matrix, proof))
            for bad in mutations:
                self.assertFalse(verify_nonnegative_kernel_support_certificate(matrix, bad))

    def test_cancellation_at_solver_boundary_prevents_publication(self):
        state = {'returned': False}
        def proposal(data):
            state['returned'] = True
            return [0.0]*len(data[0])
        def check():
            if state['returned']:
                raise InterruptedError('solver-boundary cancellation')
        with patch('fastunknot.sector_maximal_support._scipy_solve', side_effect=proposal):
            with self.assertRaisesRegex(InterruptedError, 'solver-boundary'):
                certify_nonnegative_kernel_support(cycle_obstruction(3), check=check)
        for after in (1, 4, 15):
            with self.assertRaises(InterruptedError):
                certify_nonnegative_kernel_support(cycle_obstruction(3), check=Cancel(after))
        proof = certify_nonnegative_kernel_support(cycle_obstruction(3))['certificate']
        with self.assertRaises(InterruptedError):
            verify_nonnegative_kernel_support_certificate(cycle_obstruction(3), proof,
                                                           check=Cancel(2))

    def test_reused_stats_are_reset_and_invalid_input_is_rejected(self):
        stats = {}
        certify_nonnegative_kernel_support(cycle_obstruction(3), stats=stats)
        with patch('fastunknot.sector_maximal_support._scipy_solve', return_value=None):
            answer = certify_nonnegative_kernel_support(cycle_obstruction(3), solver='scipy',
                                                        stats=stats)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertNotIn('solver', stats)
        self.assertNotIn('effective_dimension', stats)
        for matrix in ([[True]], [[1.0]], [[1], [1, 2]], None):
            with self.assertRaises(ValueError):
                certify_nonnegative_kernel_support(matrix)
        with self.assertRaises(ValueError):
            certify_nonnegative_kernel_support([], width=True)


class SourceSupportTests(unittest.TestCase):
    def test_genuine_fixed_row_miss_is_not_misstated_as_a_dimension_win(self):
        path = Path(__file__).with_name('fixtures')/'maximal_support_pachner_36.json'
        fixture = json.loads(path.read_text())
        raw = fixture['specification']['triangulation']
        support = fixture['allowed_types']
        source = PreparedSectorSource(raw)
        kernel = source.build(support)
        keep, _ = matching_support(kernel, lambda: None)
        maximal = certify_maximal_support(raw, support, source=source)
        self.assertEqual(len(kernel.basis), 8)
        self.assertEqual(sorted(set(keep)-set(maximal['retained_indices'])), [0])
        self.assertEqual(len(keep), 14)
        self.assertEqual(len(maximal['retained_indices']), 13)
        first_rebuild = source.build([kernel.support[j] for j in keep])
        exact_rebuild = source.build([kernel.support[j] for j in maximal['retained_indices']])
        self.assertEqual((len(first_rebuild.basis), len(exact_rebuild.basis)), (5, 5))
        second, _ = matching_support(first_rebuild, lambda: None)
        self.assertEqual([keep[j] for j in second], maximal['retained_indices'])
        self.assertTrue(verify_maximal_support_certificate(raw, support,
                                                           maximal['certificate']))

    def test_every_small_source_sector_matches_complete_raw_rays(self):
        for raw in (solid_torus(), capped_torus()):
            source = PreparedSectorSource(raw)
            for signature in product((-1, 0, 1, 2), repeat=len(raw['tetrahedra'])):
                support = [(i, q) for i, q in enumerate(signature) if q >= 0]
                kernel = source.build(support)
                rays = list(sector_rays(kernel))
                expected = [j for j, (t, q) in enumerate(support)
                            if any(row[t][4+q] for row in rays)]
                result = certify_maximal_support(raw, support, source=source)
                self.assertEqual(result['status'], 'COMPLETE')
                self.assertEqual(result['retained_indices'], expected)
                self.assertTrue(verify_maximal_support_certificate(raw, support,
                                                                   result['certificate']))
                reduced = source.build([support[j] for j in expected])
                self.assertEqual({tuple(x for row in r for x in row) for r in rays},
                                 {tuple(x for row in r for x in row) for r in sector_rays(reduced)})

    def test_raw_dimension_four_enters_planar_enumeration_before_Q_scan(self):
        raw, support = bank_fixture()
        answer = discover_in_maximal_support_sector(raw, support, max_bases=5)
        self.assertEqual(answer['status'], 'NO_VERTEX_DISC_IN_SECTOR')
        info = answer['stats']['maximal_support']
        self.assertEqual((info['raw_dimension'], info['effective_dimension']), (4, 3))
        self.assertEqual(answer['stats']['bases_attempted'], 5)
        self.assertEqual(answer['certificate']['allowed_types'], [list(x) for x in support])
        self.assertTrue(verify_sector_exhaustion(raw, answer['certificate']))
        self.assertTrue(verify_maximal_support_certificate(raw, support,
                                            answer['maximal_support_certificate']))
        limited = discover_in_maximal_support_sector(raw, support, max_bases=4)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)
        # The support proof alone is valid even when ray discovery is capped.
        self.assertTrue(verify_maximal_support_certificate(raw, support,
                                            limited['maximal_support_certificate']))

    def test_existing_positive_witness_protocol_and_safe_solver_fallback(self):
        raw = solid_torus()
        answer = discover_in_maximal_support_sector(raw, [(0, 2)], max_orbit_cycles=0)
        self.assertEqual(answer['status'], 'DISC_FOUND')
        self.assertTrue(verify_sector_witness(raw, answer['certificate']))
        raw, support = bank_fixture()
        with patch('fastunknot.sector_maximal_support._scipy_solve', return_value=None):
            failed = discover_in_maximal_support_sector(raw, support, solver='scipy')
        incumbent = discover_in_sector(raw, support, phase='standard')
        self.assertEqual(failed['status'], incumbent['status'])
        self.assertEqual(failed['certificate'], incumbent['certificate'])
        self.assertNotIn('maximal_support_certificate', failed)

    def test_source_checker_uses_only_source_rows_and_rejects_proof_mutations(self):
        raw, support = bank_fixture()
        proof = certify_maximal_support(raw, support)['certificate']
        mutations = []
        bad = deepcopy(proof); bad['primal_coordinates'][0][0] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['row_combination'].clear(); mutations.append(bad)
        bad = deepcopy(proof); bad['row_combination'][0][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['row_combination'][0][2] = 0; mutations.append(bad)
        bad = deepcopy(proof); bad['row_combination'].append(bad['row_combination'][0]); mutations.append(bad)
        bad = deepcopy(proof); bad['row_combination'][0][0] = True; mutations.append(bad)
        bad = deepcopy(proof); bad['allowed_types'].reverse(); mutations.append(bad)
        bad = deepcopy(proof); bad['retained_indices'].reverse(); mutations.append(bad)
        bad = deepcopy(proof); bad['source_sha256'] = '0'*64; mutations.append(bad)
        disabled = ('fastunknot.sector_sparse.PreparedSectorSource',
                    'fastunknot.normal_sector.build_sector_kernel',
                    'fastunknot.sector_maximal_support._partition',
                    'fastunknot.sector_matching_support._source_constraints',
                    'fastunknot.normal_sector._rref')
        with ExitStack() as stack:
            for name in disabled:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_maximal_support_certificate(raw, support, proof))
            for bad in mutations:
                self.assertFalse(verify_maximal_support_certificate(raw, support, bad))

    def test_empty_nonzero_cone_support_order_and_source_identity(self):
        raw, support = bank_fixture()
        source = PreparedSectorSource(raw)
        a = certify_maximal_support(raw, support, source=source)
        b = certify_maximal_support(raw, list(reversed(support)), source=source)
        self.assertEqual(a['certificate'], b['certificate'])
        self.assertTrue(verify_maximal_support_certificate(raw, list(reversed(support)),
                                                          b['certificate']))
        empty = certify_maximal_support(raw, [], source=source)
        self.assertEqual(empty['retained_indices'], [])
        self.assertTrue(verify_maximal_support_certificate(raw, [], empty['certificate']))
        with self.assertRaises(ValueError):
            certify_maximal_support(solid_torus(), [], source=source)
        before = deepcopy(raw)
        with self.assertRaises(InterruptedError):
            certify_maximal_support(raw, support, source=source, check=Cancel(5))
        self.assertEqual(raw, before)
        self.assertEqual(certify_maximal_support(raw, support, source=source)['status'], 'COMPLETE')
        with self.assertRaises(InterruptedError):
            verify_maximal_support_certificate(raw, support, a['certificate'], check=Cancel(3))
        calls = [0]
        def callback_with_geometry_exception():
            calls[0] += 1
            if calls[0] == 3:
                raise NormalOrbitError('caller cancellation, not invalid geometry')
        with self.assertRaisesRegex(NormalOrbitError, 'caller cancellation'):
            verify_maximal_support_certificate(raw, support, a['certificate'],
                                               check=callback_with_geometry_exception)


if __name__ == '__main__':
    unittest.main()
