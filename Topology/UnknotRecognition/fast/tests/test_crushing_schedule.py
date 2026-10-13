"""Fair corner scheduling, repeated-work accounting and native continuation."""
from collections import Counter
from itertools import product
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot import normal_crushing_search as search
from fastunknot.normal_sector import SearchLimit, build_sector_kernel


class SectorScheduleTests(unittest.TestCase):
    def test_prefix_and_candidate_allowances_grow_together_before_full_coverage(self):
        finished, attempts, distinct = {}, [], set()
        first = (0,)*5
        for assignment, allowance in search._sector_schedule(5, 'canonical', 2, finished, lambda: None):
            distinct.add(assignment)
            if assignment == first:
                attempts.append((allowance, len(distinct)))
                if allowance >= 17:
                    break
            else:
                finished[assignment] = True
        self.assertEqual(attempts, [(2, 1), (4, 16), (8, 32), (16, 64), (32, 128)])
        self.assertLess(len(distinct), 3**5)

    def test_completed_jobs_skip_retries_and_doubling_charges_less_than_three_times_work(self):
        for order in ('canonical', 'diversified'):
            finished, visits, costs = {}, Counter(), Counter()
            work = {a: i % 13 for i, a in enumerate(product(range(3), repeat=3))}
            for assignment, allowance in search._sector_schedule(3, order, 1, finished, lambda: None):
                self.assertNotIn(assignment, finished)
                visits[assignment] += 1
                costs[assignment] += min(allowance, work[assignment])
                if allowance >= work[assignment]:
                    finished[assignment] = True
            self.assertEqual(sorted(finished), list(product(range(3), repeat=3)))
            for assignment, total in costs.items():
                self.assertLessEqual(total, 3*work[assignment])
                if work[assignment] <= 1:
                    self.assertEqual(visits[assignment], 1)
            self.assertGreater(max(visits.values()), 1)

    def test_none_preserves_sequential_order_and_invalid_quantum_is_rejected(self):
        expected = list(search._sector_assignments(3, 'diversified', lambda: None))
        actual = list(search._sector_schedule(3, 'diversified', None, {}, lambda: None))
        self.assertEqual(actual, [(assignment, None) for assignment in expected])
        for quantum in (False, True, 0, -1, 0.5, '64'):
            with self.assertRaises(ValueError):
                recognize_by_crushing(Diagram.from_pd([]), sector_quantum=quantum)


class CornerRestartTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_pd([])
        result = recognize_by_crushing(cls.diagram, sector_order='canonical', sector_quantum=None)
        cls.coordinates = result['certificate']['chain']['steps'][0]['coordinates']

    def enumerator(self, *, always_unfinished=False, attempts=None):
        """Synthetic candidate costs, but a genuinely source-checked positive ray.

        Fake completed jobs are not used as geometric evidence: the positive
        verdict replays its real ray/quotient; partial runs claim no negative.
        """
        attempts = [] if attempts is None else attempts
        def rays(kernel, *, phase, method, max_bases, stats, check):
            assignment = tuple(q for _, q in kernel.support)
            attempts.append((assignment, max_bases))
            stats['bases_attempted'] = 0
            if assignment != (0,)*5 and not always_unfinished:
                return
            cost = max_bases+1 if always_unfinished else 9
            for _ in range(cost):
                check()
                if max_bases is not None and stats['bases_attempted'] >= max_bases:
                    raise SearchLimit('candidate-basis allowance exhausted')
                stats['bases_attempted'] += 1
            yield self.coordinates
        return rays

    def test_restarts_cache_preparation_and_charge_all_repeated_candidates(self):
        attempts = []
        with patch('fastunknot.normal_sector.sector_rays', self.enumerator(attempts=attempts)), \
             patch('fastunknot.sector_matching_support.matching_support',
                   side_effect=lambda kernel, check: (list(range(len(kernel.support))), None)), \
             patch('fastunknot.normal_sector.build_sector_kernel', wraps=build_sector_kernel) as prepare:
            result = recognize_by_crushing(self.diagram, sector_order='canonical', sector_quantum=2,
                                          max_sectors=64, max_bases=None)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertTrue(verify_crushing_recognition(self.diagram, result['certificate']))
        self.assertEqual([q for a, q in attempts if a == (0,)*5], [2, 4, 8, 16])
        self.assertEqual(result['stats']['bases_attempted'], 2+4+8+9)
        self.assertEqual(result['stats']['sectors_attempted'], 64)
        self.assertEqual(result['stats']['sector_restarts'], 3)
        self.assertEqual(result['stats']['sector_quantum_exhaustions'], 3)
        self.assertEqual(prepare.call_count, 64)
        self.assertEqual(result['stats']['max_cached_sector_jobs'], 2)

    def test_shared_basis_cap_counts_retry_work_and_never_emits_a_partial_negative(self):
        attempts = []
        with patch('fastunknot.normal_sector.sector_rays', self.enumerator(attempts=attempts)), \
             patch('fastunknot.sector_matching_support.matching_support',
                   side_effect=lambda kernel, check: (list(range(len(kernel.support))), None)):
            result = recognize_by_crushing(self.diagram, sector_order='canonical', sector_quantum=2,
                                          max_sectors=16, max_bases=5)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        self.assertEqual(result['stats']['bases_attempted'], 5)
        self.assertEqual(result['stats']['sectors_attempted'], 16)
        self.assertEqual(result['stats']['sector_restarts'], 1)
        self.assertEqual([q for a, q in attempts if a == (0,)*5], [2, 3])
        self.assertTrue(verify_crushing_chain(self.diagram, result['partial_chain']))

    def test_all_unfinished_jobs_cannot_be_mistaken_for_exhausted_sectors(self):
        with patch('fastunknot.normal_sector.sector_rays', self.enumerator(always_unfinished=True)), \
             patch('fastunknot.sector_matching_support.matching_support',
                   side_effect=lambda kernel, check: (list(range(len(kernel.support))), None)):
            result = recognize_by_crushing(self.diagram, sector_order='canonical', sector_quantum=2,
                                          max_sectors=None, max_bases=33)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['bases_attempted'], 33)
        self.assertEqual(result['stats']['sectors_attempted'], 16)
        self.assertEqual(result['stats']['sector_restarts'], 1)
        self.assertEqual(result['partial_chain']['steps'], [])
        self.assertNotIn('certificate', result)

    def test_restarted_negative_jobs_still_require_exact_coverage_and_independent_replay(self):
        # A lying producer finishes every sector after three candidates. Fair
        # scheduling must cover all sectors exactly once in the final packet,
        # but independent geometric replay must still reject the false result.
        observed, charges = [], []
        def rays(kernel, *, phase, method, max_bases, stats, check):
            stats['bases_attempted'] = 0
            for _ in range(3):
                check()
                if stats['bases_attempted'] >= max_bases:
                    raise SearchLimit('synthetic local allowance exhausted')
                stats['bases_attempted'] += 1
                charges.append(1)
            yield from ()
        def replay(diagram, proof, *, check):
            observed.append(proof)
            self.assertEqual([p['allowed_types'] for p in proof['exhaustion']],
                [[[t, q] for t, q in enumerate(a)] for a in product(range(3), repeat=5)])
            return verify_crushing_recognition(diagram, proof, check=check)
        with patch('fastunknot.normal_sector.sector_rays', rays), \
             patch.object(search, 'verify_crushing_recognition', replay):
            with self.assertRaisesRegex(ArithmeticError, 'recognition replay failed'):
                recognize_by_crushing(self.diagram, sector_quantum=2,
                                      max_sectors=None, max_bases=None)
        self.assertEqual(len(observed), 1)
        self.assertEqual(len(charges), 3*3**5+2*16)

    def test_caller_searchlimit_during_a_restart_propagates_as_the_same_exception(self):
        attempts = []
        error = SearchLimit('caller cancellation during restarted job')
        def check():
            if sum(a == (0,)*5 for a, _ in attempts) > 1:
                raise error
        with patch('fastunknot.normal_sector.sector_rays', self.enumerator(attempts=attempts)), \
             patch('fastunknot.sector_matching_support.matching_support',
                   side_effect=lambda kernel, check: (list(range(len(kernel.support))), None)):
            with self.assertRaises(SearchLimit) as caught:
                recognize_by_crushing(self.diagram, sector_order='canonical', sector_quantum=2,
                                      max_sectors=16, max_bases=None, check=check)
        self.assertIs(caught.exception, error)

    def test_native_trefoil_progresses_beyond_the_hard_44_tetrahedron_first_sector(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        result = recognize_by_crushing(diagram, max_sectors=5, max_bases=128, sector_quantum=64)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['sectors_attempted'], 5)
        self.assertEqual(result['stats']['bases_attempted'], 3+64+7)
        self.assertEqual(result['stats']['sector_quantum_exhaustions'], 1)
        self.assertEqual(result['stats']['crushing_steps'], 3)
        self.assertEqual([len(step['successor']['tetrahedra'])
                          for step in result['partial_chain']['steps']], [46, 44, 42])
        self.assertTrue(verify_crushing_chain(diagram, result['partial_chain']))


if __name__ == '__main__':
    unittest.main()
